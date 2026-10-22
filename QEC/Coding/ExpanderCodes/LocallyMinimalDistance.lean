import QEC.Coding.Core.Definitions
import Mathlib.Order.Lattice.Nat

/-!
# Local minimality and quotient distance

This weighted-group reduction is the first assertion of
[PK22, Lemma `dist-from-lm`, `main.tex:805-818`]. A minimum-weight
representative of a nonzero class modulo boundaries is locally minimal under
every chosen boundary move. Consequently, a lower bound for all nonzero locally
minimal cycles bounds every nontrivial homology class.

The result does not supply a locally-minimal lower bound for the PK22
construction; that is the separate expansion argument.
-/

namespace QEC.Coding.LocallyMinimalDistance

universe u v

variable {C : Type*} [AddCommGroup C]

/-- A chain is locally minimal for a finite family of allowed moves. -/
def IsLocallyMinimal (weight : C → Nat) (moves : Finset C) (c : C) : Prop :=
  ∀ m ∈ moves, weight c ≤ weight (c + m)

/-- The minimum weight among representatives of the class of `c` modulo `B`. -/
noncomputable def cosetWeight (weight : C → Nat) (B : AddSubgroup C) (c : C) : Nat :=
  sInf {n : Nat | ∃ b ∈ B, weight (c + b) = n}

/-- A finite-weight coset has a representative attaining its quotient weight. -/
theorem exists_minimal_coset_representative
    (weight : C → Nat) (B : AddSubgroup C) (c : C) :
    ∃ b ∈ B, weight (c + b) = cosetWeight weight B c := by
  have hnonempty : {n : Nat | ∃ b ∈ B, weight (c + b) = n}.Nonempty := by
    refine ⟨weight (c + 0), ?_⟩
    exact ⟨0, B.zero_mem, rfl⟩
  exact Nat.sInf_mem hnonempty

/-- A minimum-weight coset representative is locally minimal under boundary moves. -/
theorem minimal_coset_representative_isLocallyMinimal
    (weight : C → Nat) (B : AddSubgroup C) (moves : Finset C)
    (hmoves : ∀ m ∈ moves, m ∈ B) (c b : C) (hb : b ∈ B)
    (hmin : weight (c + b) = cosetWeight weight B c) :
    IsLocallyMinimal weight moves (c + b) := by
  intro m hm
  have hle : cosetWeight weight B c ≤ weight (c + (b + m)) := by
    apply Nat.sInf_le
    exact ⟨b + m, B.add_mem hb (hmoves m hm), rfl⟩
  rw [hmin]
  simpa only [add_assoc] using hle

/-- A non-boundary cycle has a nonzero, locally minimal coset representative. -/
theorem exists_nonzero_locallyMinimal_cycle
    (weight : C → Nat) (Z B : AddSubgroup C) (moves : Finset C)
    (hBZ : B ≤ Z) (hmoves : ∀ m ∈ moves, m ∈ B)
    (c : C) (hcZ : c ∈ Z) (hcB : c ∉ B) :
    ∃ c' : C, c' ∈ Z ∧ c' ≠ 0 ∧ IsLocallyMinimal weight moves c' ∧
      weight c' ≤ weight c := by
  obtain ⟨b, hb, hmin⟩ := exists_minimal_coset_representative weight B c
  refine ⟨c + b, Z.add_mem hcZ (hBZ hb), ?_,
    minimal_coset_representative_isLocallyMinimal weight B moves hmoves c b hb hmin,
    ?_⟩
  · intro hzero
    apply hcB
    have hc : c = -b := by
      exact eq_neg_of_add_eq_zero_left hzero
    rw [hc]
    exact B.neg_mem hb
  · rw [hmin]
    apply Nat.sInf_le
    exact ⟨0, B.zero_mem, by simp⟩

/-- A local-minimal cycle bound transfers to all nontrivial homology classes. -/
theorem weight_ge_of_locallyMinimal_cycle_bound
    (weight : C → Nat) (Z B : AddSubgroup C) (moves : Finset C)
    (hBZ : B ≤ Z) (hmoves : ∀ m ∈ moves, m ∈ B)
    (lowerBound : Nat)
    (hlocal : ∀ c : C, c ∈ Z → c ≠ 0 →
      IsLocallyMinimal weight moves c → lowerBound ≤ weight c)
    (c : C) (hcZ : c ∈ Z) (hcB : c ∉ B) :
    lowerBound ≤ weight c := by
  obtain ⟨c', hc'Z, hc'0, hc'local, hc'le⟩ :=
    exists_nonzero_locallyMinimal_cycle weight Z B moves hBZ hmoves c hcZ hcB
  exact (hlocal c' hc'Z hc'0 hc'local).trans hc'le

/-!
The following corollary is the chain-complex use site of the quotient-group
reduction. Its local moves are the images of individual scalar basis chains
under the second boundary. The PK22 construction must subsequently establish
`hlocal` for its specific weighted lifted-product complex and also for its dual.
-/

/-- Images of elementary degree-two chains under the second boundary. -/
noncomputable def elementaryBoundaryMoves
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    Finset (Word F ι) := by
  classical
  exact Finset.univ.image
    (fun p : κ₂ × F => K.boundary2 (p.2 • canonicalBasisWord p.1))

/-- Every elementary boundary move is an actual middle boundary. -/
theorem elementaryBoundaryMoves_subset_middleBoundaryCode
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (m : Word F ι) (hm : m ∈ elementaryBoundaryMoves K) :
    m ∈ K.middleBoundaryCode.carrier := by
  classical
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
  exact (K.mem_middleBoundaryCode_iff _).2
    ⟨p.2 • canonicalBasisWord p.1, rfl⟩

/-- Local minimal-cycle expansion bounds the weight of every non-boundary cycle. -/
theorem chainComplex_cycle_weight_ge_of_locallyMinimal_bound
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (weight : Word F ι → Nat)
    (lowerBound : Nat)
    (hlocal : ∀ c : Word F ι, c ∈ K.middleCycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryBoundaryMoves K) c →
        lowerBound ≤ weight c)
    (c : Word F ι) (hcZ : c ∈ K.middleCycleCode.carrier)
    (hcB : c ∉ K.middleBoundaryCode.carrier) :
    lowerBound ≤ weight c := by
  exact weight_ge_of_locallyMinimal_cycle_bound weight
    K.middleCycleCode.carrier.toAddSubgroup
    K.middleBoundaryCode.carrier.toAddSubgroup (elementaryBoundaryMoves K)
    K.middleBoundaryCode_le_middleCycleCode
    (elementaryBoundaryMoves_subset_middleBoundaryCode K) lowerBound hlocal
    c hcZ hcB

/-- Images of elementary degree-zero cochains under the first coboundary. -/
noncomputable def elementaryCoboundaryMoves
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    Finset (Word F ι) := by
  classical
  exact Finset.univ.image
    (fun p : κ₀ × F =>
      wordLinearMapTranspose K.boundary1 (p.2 • canonicalBasisWord p.1))

/-- Every elementary coboundary move belongs to the first coboundary code. -/
theorem elementaryCoboundaryMoves_subset_firstCoboundaryCheckCode
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (m : Word F ι) (hm : m ∈ elementaryCoboundaryMoves K) :
    m ∈ K.firstCoboundaryCheckCode.carrier := by
  classical
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
  exact (K.mem_firstCoboundaryCheckCode_iff _).2
    ⟨p.2 • canonicalBasisWord p.1, rfl⟩

/-- The dual local-minimal bound controls every non-coboundary cocycle. -/
theorem chainComplex_cocycle_weight_ge_of_locallyMinimal_bound
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (weight : Word F ι → Nat) (lowerBound : Nat)
    (hlocal : ∀ c : Word F ι, c ∈ K.middleCocycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryCoboundaryMoves K) c →
        lowerBound ≤ weight c)
    (c : Word F ι) (hcZ : c ∈ K.middleCocycleCode.carrier)
    (hcB : c ∉ K.firstCoboundaryCheckCode.carrier) :
    lowerBound ≤ weight c := by
  exact weight_ge_of_locallyMinimal_cycle_bound weight
    K.middleCocycleCode.carrier.toAddSubgroup
    K.firstCoboundaryCheckCode.carrier.toAddSubgroup
    (elementaryCoboundaryMoves K)
    K.firstCoboundaryCheckCode_le_middleCocycleCode
    (elementaryCoboundaryMoves_subset_firstCoboundaryCheckCode K)
    lowerBound hlocal c hcZ hcB

/-- Primal and dual locally minimal expansion bound algebraic CSS distance. -/
theorem chainComplex_algebraicCSSMinimumDistance_ge_of_locallyMinimal_bounds
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (weight : Word F ι → Nat) (lowerBound d : Nat)
    (hweight : ∀ c : Word F ι, weight c ≤ HammingWeight c)
    (hcycles : ∀ c : Word F ι, c ∈ K.middleCycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryBoundaryMoves K) c →
        lowerBound ≤ weight c)
    (hcocycles : ∀ c : Word F ι, c ∈ K.middleCocycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryCoboundaryMoves K) c →
        lowerBound ≤ weight c)
    (hminimum : AlgebraicCSSMinimumDistance
      K.firstCoboundaryCheckCode K.middleBoundaryCode d) :
    lowerBound ≤ d := by
  rcases hminimum with ⟨c, hc, hdistance, _⟩
  rw [← hdistance]
  rcases hc with hcX | hcZ
  · have hcCocycle : c ∈ K.middleCocycleCode.carrier := by
      rw [← K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
      exact hcX.1
    exact (chainComplex_cocycle_weight_ge_of_locallyMinimal_bound
      K weight lowerBound hcocycles c hcCocycle hcX.2).trans (hweight c)
  · have hcCycle : c ∈ K.middleCycleCode.carrier := by
      rw [← K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
      exact hcZ.1
    exact (chainComplex_cycle_weight_ge_of_locallyMinimal_bound
      K weight lowerBound hcycles c hcCycle hcZ.2).trans (hweight c)

end QEC.Coding.LocallyMinimalDistance
