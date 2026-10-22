import QEC.Coding.FourDimensionalToricCode.LogicalSectors
import QEC.Coding.Stabilizer.Energy

/-!
# Partial-membrane syndrome loops in the four-dimensional toric code

This module supplies the DKLP02 geometric bridge left open by the selected-term
energy API.  A partial primal membrane has link syndrome `boundary2 m`; a
partial dual membrane, represented on primal plaquette qubits, has cube
syndrome `boundary3ᵀ m`.  The chain-complex identities make both syndromes
closed, and their Hamming lengths are exactly the violated-check counts.

With the BT09 unit-coefficient Hamiltonian convention already fixed in
`StabilizerEnergy`, the corresponding excess energy is twice the loop length.
No asymptotic barrier lower bound or membrane-sweep construction is asserted
here; those are the downstream #569 and #570 obligations.

[DKLP02, Section "Toric code in four dimensions", `sec:four_dim`]
[BT09, Section III]
-/

noncomputable section

namespace QEC.Coding.PeriodicCubical4

open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian

variable {L : Nat} [NeZero L] [Fact (1 < L)]

/-- A partial primal membrane is represented by its plaquette 2-chain. -/
abbrev PartialPrimalMembrane := Word (ZMod 2) (Plaquette L)

/-- A partial dual membrane is represented on the same primal plaquette qubits. -/
abbrev PartialDualMembrane := Word (ZMod 2) (Plaquette L)

/-- The link-check defect loop bounding a partial primal membrane. -/
def primalDefectLoop (m : PartialPrimalMembrane (L := L)) :
    Word (ZMod 2) (Link L) :=
  boundary2 m

/-- The cube-check defect loop bounding a partial dual membrane. -/
def dualDefectLoop (m : PartialDualMembrane (L := L)) :
    Word (ZMod 2) (Cube L) :=
  wordLinearMapTranspose boundary3 m

/-- DKLP unit-energy length of the primal defect loop. -/
def primalLoopLength (m : PartialPrimalMembrane (L := L)) : Nat :=
  HammingWeight (primalDefectLoop m)

/-- DKLP unit-energy length of the dual defect loop. -/
def dualLoopLength (m : PartialDualMembrane (L := L)) : Nat :=
  HammingWeight (dualDefectLoop m)

/-- The pure-Z Pauli error supported on a partial primal membrane. -/
def primalMembraneError (m : PartialPrimalMembrane (L := L)) :
    Binary (Plaquette L) :=
  cssZCheck m

/-- The pure-X Pauli error supported on a partial dual membrane. -/
def dualMembraneError (m : PartialDualMembrane (L := L)) :
    Binary (Plaquette L) :=
  cssXCheck m

/-- The exact selected-generator syndrome of a partial primal membrane. -/
theorem toricSyndrome_primalMembrane (m : PartialPrimalMembrane (L := L)) :
    stabilizerSyndrome (toricGenerator (L := L)) (primalMembraneError m) =
      Sum.elim (primalDefectLoop m) (0 : Word (ZMod 2) (Cube L)) := by
  funext j
  cases j with
  | inl e =>
      simp [primalMembraneError, stabilizerSyndrome,
        stabilizerSyndromeBit, symplecticForm]
      change wordPairing m
        (wordLinearMapTranspose boundary2 (Pi.single e 1)) = boundary2 m e
      rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply,
        wordPairing_wordLinearMapTranspose]
      simp [wordPairing_apply]
  | inr c =>
      simp [primalMembraneError, stabilizerSyndrome, stabilizerSyndromeBit,
        symplecticForm]

/-- The exact selected-generator syndrome of a partial dual membrane. -/
theorem toricSyndrome_dualMembrane (m : PartialDualMembrane (L := L)) :
    stabilizerSyndrome (toricGenerator (L := L)) (dualMembraneError m) =
      Sum.elim (0 : Word (ZMod 2) (Link L)) (dualDefectLoop m) := by
  funext j
  cases j with
  | inl e =>
      simp [dualMembraneError, stabilizerSyndrome, stabilizerSyndromeBit,
        symplecticForm]
  | inr c =>
      simp [dualMembraneError, stabilizerSyndrome,
        stabilizerSyndromeBit, symplecticForm]
      change wordPairing m (boundary3 (Pi.single c 1)) =
        wordLinearMapTranspose boundary3 m c
      rw [← wordPairing_wordLinearMapTranspose]
      simp [wordPairing_apply, dotProduct_comm]

/-- A primal membrane syndrome is a closed link loop. -/
theorem boundary1_primalDefectLoop (m : PartialPrimalMembrane (L := L)) :
    boundary1 (primalDefectLoop m) = 0 := by
  change ((boundary1 (L := L)).comp boundary2) m = 0
  rw [boundary1_comp_boundary2]
  rfl

/-- A dual membrane syndrome is a closed dual-link loop (a cube 1-chain). -/
theorem transpose_boundary4_dualDefectLoop (m : PartialDualMembrane (L := L)) :
    wordLinearMapTranspose boundary4 (dualDefectLoop m) = 0 := by
  apply (wordPairing_nondegenerate (F := ZMod 2)).left
  intro h
  rw [wordPairing_wordLinearMapTranspose, dualDefectLoop,
    wordPairing_wordLinearMapTranspose]
  have hzero : boundary3 (boundary4 h) = 0 := by
    change ((boundary3 (L := L)).comp boundary4) h = 0
    rw [boundary3_comp_boundary4]
    rfl
  rw [hzero]
  simp

/-- The selected syndrome support is the tagged support of the primal loop. -/
theorem syndromeSupport_primalMembrane (m : PartialPrimalMembrane (L := L)) :
    (toricHamiltonian (L := L)).syndromeSupport (primalMembraneError m) =
      (hammingSupport (primalDefectLoop m)).map
        ⟨Sum.inl, Sum.inl_injective⟩ := by
  ext j
  cases j with
  | inl e =>
      rw [mem_syndromeSupport, toricHamiltonian_generators,
        toricSyndrome_primalMembrane]
      simp only [Sum.elim_inl, Finset.mem_map, hammingSupport,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨e, ?_, rfl⟩
        simp [h]
      · rintro ⟨e', he', hinj⟩
        cases Sum.inl.inj hinj
        exact zmod_two_eq_one_of_ne_zero he'
  | inr c =>
      rw [mem_syndromeSupport, toricHamiltonian_generators,
        toricSyndrome_primalMembrane]
      simp

/-- The selected syndrome support is the tagged support of the dual loop. -/
theorem syndromeSupport_dualMembrane (m : PartialDualMembrane (L := L)) :
    (toricHamiltonian (L := L)).syndromeSupport (dualMembraneError m) =
      (hammingSupport (dualDefectLoop m)).map
        ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext j
  cases j with
  | inl e =>
      rw [mem_syndromeSupport, toricHamiltonian_generators,
        toricSyndrome_dualMembrane]
      simp
  | inr c =>
      rw [mem_syndromeSupport, toricHamiltonian_generators,
        toricSyndrome_dualMembrane]
      simp only [Sum.elim_inr, Finset.mem_map, hammingSupport,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨c, ?_, rfl⟩
        simp [h]
      · rintro ⟨c', hc', hinj⟩
        cases Sum.inr.inj hinj
        exact zmod_two_eq_one_of_ne_zero hc'

/-- DKLP unit defect energy is exactly primal syndrome-loop length. -/
theorem unitDefectEnergy_primalMembrane (m : PartialPrimalMembrane (L := L)) :
    (toricHamiltonian (L := L)).unitDefectEnergy (primalMembraneError m) =
      primalLoopLength m := by
  rw [unitDefectEnergy_eq_syndromeWeight, syndromeWeight,
    syndromeSupport_primalMembrane]
  simp [primalLoopLength, HammingWeight]

/-- DKLP unit defect energy is exactly dual syndrome-loop length. -/
theorem unitDefectEnergy_dualMembrane (m : PartialDualMembrane (L := L)) :
    (toricHamiltonian (L := L)).unitDefectEnergy (dualMembraneError m) =
      dualLoopLength m := by
  rw [unitDefectEnergy_eq_syndromeWeight, syndromeWeight,
    syndromeSupport_dualMembrane]
  simp [dualLoopLength, HammingWeight]

/-- BT09 excess energy is twice the primal DKLP loop length. -/
theorem btExcessEnergy_primalMembrane (m : PartialPrimalMembrane (L := L)) :
    (toricHamiltonian (L := L)).btExcessEnergy (primalMembraneError m) =
      2 * primalLoopLength m := by
  rw [btExcessEnergy_eq_two_mul_unitDefectEnergy,
    unitDefectEnergy_primalMembrane]

/-- BT09 excess energy is twice the dual DKLP loop length. -/
theorem btExcessEnergy_dualMembrane (m : PartialDualMembrane (L := L)) :
    (toricHamiltonian (L := L)).btExcessEnergy (dualMembraneError m) =
      2 * dualLoopLength m := by
  rw [btExcessEnergy_eq_two_mul_unitDefectEnergy,
    unitDefectEnergy_dualMembrane]

/-- The support of one primal plaquette boundary is its incident-link set. -/
theorem hammingSupport_plaquetteBoundary (p : Plaquette L) :
    hammingSupport (plaquetteBoundary p) = plaquetteLinks p := by
  ext e
  calc
    e ∈ hammingSupport (plaquetteBoundary p) ↔
        wordLinearMapTranspose boundary2 (Pi.single e 1) p ≠ 0 := by
          simp [hammingSupport, transpose_boundary2_single_apply]
    _ ↔ p ∈ linkPlaquettes e := by
      rw [← hammingSupport_transpose_boundary2_single e]
      simp [hammingSupport]
    _ ↔ e ∈ plaquetteLinks p := mem_linkPlaquettes_iff_mem_plaquetteLinks e p

/-- Transposing the cube boundary evaluates a plaquette against that boundary. -/
theorem transpose_boundary3_cellWord_apply (p : Plaquette L) (c : Cube L) :
    wordLinearMapTranspose boundary3 (cellWord p) c = cubeBoundary c p := by
  calc
    wordLinearMapTranspose boundary3 (cellWord p) c =
        wordPairing (wordLinearMapTranspose boundary3 (cellWord p))
          (Pi.single c 1) := by
            simp [wordPairing_apply, dotProduct_comm]
    _ = wordPairing (cellWord p) (boundary3 (Pi.single c 1)) :=
      wordPairing_wordLinearMapTranspose boundary3 (cellWord p) (Pi.single c 1)
    _ = cubeBoundary c p := by
      classical
      simp only [boundary3, linearize_single, wordPairing_apply, dotProduct,
        cellWord]
      rw [Fintype.sum_eq_single p]
      · simp
      · intro q hqp
        simp [hqp]

/-- The support of one dual plaquette coboundary is its incident-cube set. -/
theorem hammingSupport_transpose_boundary3_cellWord (p : Plaquette L) :
    hammingSupport (wordLinearMapTranspose boundary3 (cellWord p)) =
      plaquetteCubes p := by
  ext c
  calc
    c ∈ hammingSupport (wordLinearMapTranspose boundary3 (cellWord p)) ↔
        cubeBoundary c p ≠ 0 := by
          simp [hammingSupport, transpose_boundary3_cellWord_apply]
    _ ↔ p ∈ cubePlaquettes c := by
      rw [← hammingSupport_cubeBoundary c]
      simp [hammingSupport]
    _ ↔ c ∈ plaquetteCubes p := mem_cubePlaquettes_iff_mem_plaquetteCubes c p

/-- A single primal plaquette has at most four boundary-link defects. -/
theorem HammingWeight_plaquetteBoundary_le_four (p : Plaquette L) :
    HammingWeight (plaquetteBoundary p) ≤ 4 := by
  simpa [HammingWeight, hammingSupport_plaquetteBoundary] using
    card_plaquetteLinks_le_four p

/-- A single dual plaquette has at most four incident-cube defects. -/
theorem HammingWeight_transpose_boundary3_cellWord_le_four (p : Plaquette L) :
    HammingWeight (wordLinearMapTranspose boundary3 (cellWord p)) ≤ 4 := by
  simpa [HammingWeight, hammingSupport_transpose_boundary3_cellWord] using
    card_plaquetteCubes_le_four p

/-- Toggling one primal plaquette toggles exactly its four boundary links. -/
theorem primalDefectLoop_add_plaquette
    (m : PartialPrimalMembrane (L := L)) (p : Plaquette L) :
    primalDefectLoop (m + cellWord p) =
      primalDefectLoop m + plaquetteBoundary p := by
  simp [primalDefectLoop, boundary2, linearize_cellWord]

/-- Toggling one dual plaquette toggles exactly its incident dual links. -/
theorem dualDefectLoop_add_plaquette
    (m : PartialDualMembrane (L := L)) (p : Plaquette L) :
    dualDefectLoop (m + cellWord p) =
      dualDefectLoop m + wordLinearMapTranspose boundary3 (cellWord p) := by
  simp [dualDefectLoop]

/-- The partial-membrane Pauli itself is updated by one pure-Z plaquette. -/
theorem primalMembraneError_add_plaquette
    (m : PartialPrimalMembrane (L := L)) (p : Plaquette L) :
    binaryMul (primalMembraneError m) (primalMembraneError (cellWord p)) =
      primalMembraneError (m + cellWord p) := by
  simp [primalMembraneError]

/-- The partial-membrane Pauli itself is updated by one pure-X plaquette. -/
theorem dualMembraneError_add_plaquette
    (m : PartialDualMembrane (L := L)) (p : Plaquette L) :
    binaryMul (dualMembraneError m) (dualMembraneError (cellWord p)) =
      dualMembraneError (m + cellWord p) := by
  simp [dualMembraneError]

/-- One primal plaquette step can increase loop length by at most four. -/
theorem primalLoopLength_add_plaquette_le
    (m : PartialPrimalMembrane (L := L)) (p : Plaquette L) :
    primalLoopLength (m + cellWord p) ≤ primalLoopLength m + 4 := by
  rw [primalLoopLength, primalDefectLoop_add_plaquette, primalLoopLength]
  exact le_trans
    (HammingWeight_add_le (primalDefectLoop m) (plaquetteBoundary p))
    (Nat.add_le_add_left (HammingWeight_plaquetteBoundary_le_four p) _)

/-- One dual plaquette step can increase loop length by at most four. -/
theorem dualLoopLength_add_plaquette_le
    (m : PartialDualMembrane (L := L)) (p : Plaquette L) :
    dualLoopLength (m + cellWord p) ≤ dualLoopLength m + 4 := by
  rw [dualLoopLength, dualDefectLoop_add_plaquette, dualLoopLength]
  exact le_trans
    (HammingWeight_add_le (dualDefectLoop m)
      (wordLinearMapTranspose boundary3 (cellWord p)))
    (Nat.add_le_add_left
      (HammingWeight_transpose_boundary3_cellWord_le_four p) _)

end QEC.Coding.PeriodicCubical4
