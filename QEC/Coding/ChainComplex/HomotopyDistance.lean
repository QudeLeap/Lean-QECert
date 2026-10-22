import QEC.Coding.ChainComplex.Cohomology

/-!
# Distance transport across three-term chain-homotopy equivalences

HHO20 Appendix A uses explicit chain-homotopy equivalences whose middle maps
are Lipschitz for Hamming weight.  This module packages the exact consequence:
homological and cohomological distance lower bounds survive, with the expected
division by the Lipschitz constant.
-/

namespace QEC.Coding

universe u v w

/-- Every nontrivial middle homology representative has Hamming weight at
least `d`. -/
def MiddleHomologyDistanceAtLeast
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
    (K : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2))
    (d : Nat) : Prop :=
  ∀ z : Word F ι1,
    z ∈ K.middleCycleCode.carrier →
    z ∉ K.middleBoundaryCode.carrier →
    d ≤ HammingWeight z

/-- Every nontrivial middle cohomology representative has Hamming weight at
least `d`. -/
def MiddleCohomologyDistanceAtLeast
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
    (K : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2))
    (d : Nat) : Prop :=
  ∀ x : Word F ι1,
    x ∈ K.middleCocycleCode.carrier →
    x ∉ K.firstCoboundaryCheckCode.carrier →
    d ≤ HammingWeight x

namespace ThreeTermChainHomotopyEquiv

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}

omit [DecidableEq F] [Fintype ι0] [Fintype ι2] [Fintype κ0] [Fintype κ2] in
/-- The forward middle map of a chain-homotopy equivalence cannot send a
nontrivial source homology representative to a target boundary. -/
theorem forward_map1_not_mem_middleBoundaryCode
    (e : ThreeTermChainHomotopyEquiv A B)
    {z : Word F ι1}
    (hzCycle : z ∈ A.middleCycleCode.carrier)
    (hzNontrivial : z ∉ A.middleBoundaryCode.carrier) :
    e.forward.map1 z ∉ B.middleBoundaryCode.carrier := by
  intro hTargetBoundary
  let zCycle : A.middleCycleCode.carrier := ⟨z, hzCycle⟩
  have hSourceClassNe : A.middleBoundaryInCycles.mkQ zCycle ≠ 0 := by
    intro hZero
    have hMem : zCycle ∈ A.middleBoundaryInCycles :=
      (Submodule.Quotient.mk_eq_zero A.middleBoundaryInCycles).mp hZero
    exact hzNontrivial hMem
  have hTargetClassZero :
      e.forward.inducedMiddleHomology
          (A.middleBoundaryInCycles.mkQ zCycle) = 0 := by
    rw [e.forward.inducedMiddleHomology_mk]
    apply (Submodule.Quotient.mk_eq_zero B.middleBoundaryInCycles).mpr
    exact hTargetBoundary
  have hSourceClassZero : A.middleBoundaryInCycles.mkQ zCycle = 0 :=
    e.inducedMiddleHomologyEquiv.injective (by
      change e.forward.inducedMiddleHomology (A.middleBoundaryInCycles.mkQ zCycle) =
        e.forward.inducedMiddleHomology 0
      simpa only [map_zero] using hTargetClassZero)
  exact hSourceClassNe hSourceClassZero

/-- An `L`-Lipschitz forward middle map transports a target homological
distance lower bound `d` to the source lower bound `d / L`. -/
theorem middleHomologyDistanceAtLeast_of_forward_lipschitz
    (e : ThreeTermChainHomotopyEquiv A B)
    {d L : Nat}
    (hTarget : MiddleHomologyDistanceAtLeast B d)
    (hLipschitz : ∀ z : Word F ι1,
      HammingWeight (e.forward.map1 z) ≤ L * HammingWeight z) :
    MiddleHomologyDistanceAtLeast A (d / L) := by
  change ∀ z : Word F ι1,
    z ∈ A.middleCycleCode.carrier →
    z ∉ A.middleBoundaryCode.carrier →
    d / L ≤ HammingWeight z
  intro z hzCycle hzNontrivial
  apply Nat.div_le_of_le_mul
  exact (hTarget (e.forward.map1 z)
    (e.forward.mapMiddleCycle ⟨z, hzCycle⟩).2
    (e.forward_map1_not_mem_middleBoundaryCode hzCycle hzNontrivial)).trans
      (hLipschitz z)

omit [DecidableEq F] in
/-- The transpose of the inverse middle map cannot send a nontrivial source
cohomology representative to a target coboundary. -/
theorem inverse_transpose_map1_not_mem_firstCoboundaryCheckCode
    (e : ThreeTermChainHomotopyEquiv A B)
    {x : Word F ι1}
    (hxCocycle : x ∈ A.middleCocycleCode.carrier)
    (hxNontrivial : x ∉ A.firstCoboundaryCheckCode.carrier) :
    wordLinearMapTranspose e.inverse.map1 x ∉
      B.firstCoboundaryCheckCode.carrier := by
  intro hTargetCoboundary
  let xCocycle : A.middleCocycleCode.carrier := ⟨x, hxCocycle⟩
  have hSourceClassNe : A.middleCoboundaryInCocycles.mkQ xCocycle ≠ 0 := by
    intro hZero
    have hMem : xCocycle ∈ A.middleCoboundaryInCocycles :=
      (Submodule.Quotient.mk_eq_zero A.middleCoboundaryInCocycles).mp hZero
    exact hxNontrivial hMem
  have hTargetClassZero :
      e.inverse.inducedMiddleCohomology
          (A.middleCoboundaryInCocycles.mkQ xCocycle) = 0 := by
    rw [e.inverse.inducedMiddleCohomology_mk]
    apply (Submodule.Quotient.mk_eq_zero B.middleCoboundaryInCocycles).mpr
    exact hTargetCoboundary
  have hSourceClassZero : A.middleCoboundaryInCocycles.mkQ xCocycle = 0 :=
    e.inducedMiddleCohomologyEquiv.symm.injective (by
      change e.inverse.inducedMiddleCohomology (A.middleCoboundaryInCocycles.mkQ xCocycle) =
        e.inverse.inducedMiddleCohomology 0
      simpa only [map_zero] using hTargetClassZero)
  exact hSourceClassNe hSourceClassZero

/-- An `L`-Lipschitz transpose of the inverse middle map transports a target
cohomological distance lower bound `d` to the source lower bound `d / L`. -/
theorem middleCohomologyDistanceAtLeast_of_inverse_transpose_lipschitz
    (e : ThreeTermChainHomotopyEquiv A B)
    {d L : Nat}
    (hTarget : MiddleCohomologyDistanceAtLeast B d)
    (hLipschitz : ∀ x : Word F ι1,
      HammingWeight (wordLinearMapTranspose e.inverse.map1 x) ≤
        L * HammingWeight x) :
    MiddleCohomologyDistanceAtLeast A (d / L) := by
  change ∀ x : Word F ι1,
    x ∈ A.middleCocycleCode.carrier →
    x ∉ A.firstCoboundaryCheckCode.carrier →
    d / L ≤ HammingWeight x
  intro x hxCocycle hxNontrivial
  apply Nat.div_le_of_le_mul
  exact (hTarget (wordLinearMapTranspose e.inverse.map1 x)
    (e.inverse.mapMiddleCocycle ⟨x, hxCocycle⟩).2
    (e.inverse_transpose_map1_not_mem_firstCoboundaryCheckCode
      hxCocycle hxNontrivial)).trans (hLipschitz x)

end ThreeTermChainHomotopyEquiv

end QEC.Coding
