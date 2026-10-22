import QEC.Coding.ChainComplex.HomotopyDistance

/-!
# Binary CSS subsystem logical sectors

This module separates the stabilizer chain complex from a selected subsystem
logical sector.  The selected `Z` and `X` logical spaces are quotients of the
ordinary middle homology and cohomology through explicit surjective linear
maps.  Their kernels are the gauge sectors.

Distance and locality are deliberately not fields of `SubsystemCSSData`.
They remain propositions that construction modules must prove from concrete
representatives.  In particular, this interface cannot carry a dressed
distance conclusion as caller-supplied data.
-/

namespace QEC.Coding

universe u v

/--
A finite binary CSS chain complex together with selected subsystem logical
sectors.  Homology and cohomology may have additional gauge sectors, namely
the kernels of the two projections.
-/
structure SubsystemCSSData
    (i0 i1 i2 : Type u) (LogicalZ LogicalX : Type v)
    [Fintype i0] [Fintype i1] [Fintype i2]
    [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
    [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
    [Module.Finite (ZMod 2) LogicalZ] [Module.Finite (ZMod 2) LogicalX] where
  /-- The actual stabilizer chain complex. -/
  complex : ChainComplexData (ZMod 2)
    (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)
  /-- Projection from ordinary `Z` homology to the selected logical sector. -/
  homologyProjection : complex.middleHomology →ₗ[ZMod 2] LogicalZ
  /-- Projection from ordinary `X` cohomology to the selected logical sector. -/
  cohomologyProjection : complex.middleCohomology →ₗ[ZMod 2] LogicalX
  homologyProjection_surjective : Function.Surjective homologyProjection
  cohomologyProjection_surjective : Function.Surjective cohomologyProjection
  /-- The selected `Z` and `X` sectors encode the same number of qubits. -/
  logical_finrank_eq :
    Module.finrank (ZMod 2) LogicalZ = Module.finrank (ZMod 2) LogicalX

namespace SubsystemCSSData

variable {i0 i1 i2 : Type u} {LogicalZ LogicalX : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ] [Module.Finite (ZMod 2) LogicalX]

/-- The homological gauge sector discarded by the selected `Z` logical projection. -/
noncomputable def homologyGaugeSector
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    Submodule (ZMod 2) D.complex.middleHomology :=
  LinearMap.ker D.homologyProjection

/-- The cohomological gauge sector discarded by the selected `X` logical projection. -/
noncomputable def cohomologyGaugeSector
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    Submodule (ZMod 2) D.complex.middleCohomology :=
  LinearMap.ker D.cohomologyProjection

/-- Number of subsystem logical qubits, measured in the selected `Z` sector. -/
noncomputable def logicalQubits
    (_D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) : Nat :=
  Module.finrank (ZMod 2) LogicalZ

theorem logicalQubits_eq_cohomology_finrank
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    D.logicalQubits = Module.finrank (ZMod 2) LogicalX :=
  D.logical_finrank_eq

/--
Every representative whose homology class survives the selected logical
projection has weight at least `d`.  Classes in the projection kernel are
gauge operators and impose no dressed-distance obligation.
-/
def DressedZDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat) : Prop :=
  ∀ (z : Word (ZMod 2) i1)
      (hz : z ∈ D.complex.middleCycleCode.carrier),
    D.homologyProjection
        (D.complex.middleBoundaryInCycles.mkQ ⟨z, hz⟩) ≠ 0 →
      d ≤ HammingWeight z

/-- Dual dressed-distance condition for the selected cohomological sector. -/
def DressedXDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat) : Prop :=
  ∀ (x : Word (ZMod 2) i1)
      (hx : x ∈ D.complex.middleCocycleCode.carrier),
    D.cohomologyProjection
        (D.complex.middleCoboundaryInCocycles.mkQ ⟨x, hx⟩) ≠ 0 →
      d ≤ HammingWeight x

/-- Ordinary homological distance implies dressed `Z` distance for every quotient sector. -/
theorem dressedZDistanceAtLeast_of_middleHomologyDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (h : MiddleHomologyDistanceAtLeast D.complex d) :
    D.DressedZDistanceAtLeast d := by
  intro z hz hProjected
  apply h z hz
  intro hzBoundary
  apply hProjected
  have hClassZero :
      D.complex.middleBoundaryInCycles.mkQ
          (⟨z, hz⟩ : D.complex.middleCycleCode.carrier) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero
      D.complex.middleBoundaryInCycles).2
    exact hzBoundary
  rw [hClassZero, map_zero]

/--
If the homology projection is injective (in particular, for the identity
projection), dressed `Z` distance is exactly ordinary homological distance.
-/
theorem middleHomologyDistanceAtLeast_of_dressedZDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (hInjective : Function.Injective D.homologyProjection)
    (h : D.DressedZDistanceAtLeast d) :
    MiddleHomologyDistanceAtLeast D.complex d := by
  intro z hz hzNotBoundary
  apply h z hz
  intro hProjectedZero
  have hClassZero :
      D.complex.middleBoundaryInCycles.mkQ
          (⟨z, hz⟩ : D.complex.middleCycleCode.carrier) = 0 := by
    apply hInjective
    simpa using hProjectedZero
  have hzGauge :
      (⟨z, hz⟩ : D.complex.middleCycleCode.carrier) ∈
        D.complex.middleBoundaryInCycles :=
    (Submodule.Quotient.mk_eq_zero
      D.complex.middleBoundaryInCycles).1 hClassZero
  exact hzNotBoundary hzGauge

theorem dressedZDistanceAtLeast_iff_of_homologyProjection_injective
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (hInjective : Function.Injective D.homologyProjection) :
    D.DressedZDistanceAtLeast d ↔
      MiddleHomologyDistanceAtLeast D.complex d := by
  constructor
  · exact D.middleHomologyDistanceAtLeast_of_dressedZDistanceAtLeast d hInjective
  · exact D.dressedZDistanceAtLeast_of_middleHomologyDistanceAtLeast d

/-- Ordinary cohomological distance implies dressed `X` distance for every quotient sector. -/
theorem dressedXDistanceAtLeast_of_middleCohomologyDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (h : MiddleCohomologyDistanceAtLeast D.complex d) :
    D.DressedXDistanceAtLeast d := by
  intro x hx hProjected
  apply h x hx
  intro hxCoboundary
  apply hProjected
  have hClassZero :
      D.complex.middleCoboundaryInCocycles.mkQ
          (⟨x, hx⟩ : D.complex.middleCocycleCode.carrier) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero
      D.complex.middleCoboundaryInCocycles).2
    exact hxCoboundary
  rw [hClassZero, map_zero]

/-- Identity-projection adapter for the cohomological sector. -/
theorem middleCohomologyDistanceAtLeast_of_dressedXDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (hInjective : Function.Injective D.cohomologyProjection)
    (h : D.DressedXDistanceAtLeast d) :
    MiddleCohomologyDistanceAtLeast D.complex d := by
  intro x hx hxNotCoboundary
  apply h x hx
  intro hProjectedZero
  have hClassZero :
      D.complex.middleCoboundaryInCocycles.mkQ
          (⟨x, hx⟩ : D.complex.middleCocycleCode.carrier) = 0 := by
    apply hInjective
    simpa using hProjectedZero
  have hxGauge :
      (⟨x, hx⟩ : D.complex.middleCocycleCode.carrier) ∈
        D.complex.middleCoboundaryInCocycles :=
    (Submodule.Quotient.mk_eq_zero
      D.complex.middleCoboundaryInCocycles).1 hClassZero
  exact hxNotCoboundary hxGauge

theorem dressedXDistanceAtLeast_iff_of_cohomologyProjection_injective
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (hInjective : Function.Injective D.cohomologyProjection) :
    D.DressedXDistanceAtLeast d ↔
      MiddleCohomologyDistanceAtLeast D.complex d := by
  constructor
  · exact D.middleCohomologyDistanceAtLeast_of_dressedXDistanceAtLeast d hInjective
  · exact D.dressedXDistanceAtLeast_of_middleCohomologyDistanceAtLeast d

end SubsystemCSSData

end QEC.Coding
