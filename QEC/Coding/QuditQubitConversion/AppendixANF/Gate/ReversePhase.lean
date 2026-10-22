import QEC.Coding.QuditQubitConversion.AppendixANF.Gate.Data

/-!
# WHY24 Appendix-A reverse-conversion phase

The source retains the first three qubits of the selected ten-qubit resource
and measures the remaining seven in the computational basis.  This module
records that literal split and the outcome-dependent diagonal phase which
cancels the Appendix gate program except for `CCZ_{0,1,2}`.

The cancellation proof is symbolic in the two phase polynomials.  It neither
enumerates the 1024 input words nor hides such an enumeration in a decision
procedure.
-/

noncomputable section

namespace QEC.Coding

/-- Zero-based form of the source's three retained Appendix-A sites. -/
def why24AppendixRetainedSites : Finset (Fin 10) :=
  {0, 1, 2}

/-- The retained source sites are exactly `0,1,2`. -/
theorem why24AppendixRetainedSites_eq_source :
    why24AppendixRetainedSites = ({0, 1, 2} : Finset (Fin 10)) :=
  rfl

/-- The three-qubit Hilbert space left after the Appendix measurement. -/
abbrev Why24CCZSpace : Type :=
  Semantics.Qubit.QubitRegister (Fin 3)

/-- The seven measured computational-basis bits in the reverse conversion. -/
abbrev Why24AppendixReverseOutcome : Type :=
  Semantics.Qubit.Bitstring (Fin 7)

/-- The reverse conversion has exactly `2^7 = 128` measurement outcomes. -/
theorem why24AppendixReverseOutcome_card :
    Fintype.card Why24AppendixReverseOutcome = 128 := by
  rw [Semantics.Qubit.card_bitstring]
  norm_num

/-- The all-zero measured outcome. -/
def why24AppendixReverseZeroOutcome : Why24AppendixReverseOutcome :=
  fun _ => 0

/-- Recombine three retained bits and seven measured bits into the source's
ten-bit order. -/
def why24AppendixReverseRecombine
    (retained : Semantics.Qubit.Bitstring (Fin 3))
    (outcome : Why24AppendixReverseOutcome) :
    Semantics.Qubit.Bitstring (Fin 10) :=
  fun site =>
    if hsite : (site : Nat) < 3 then
      retained ⟨site, hsite⟩
    else
      outcome ⟨(site : Nat) - 3, by omega⟩

/-- The retained `CCZ` phase in the source's selected binary convention. -/
def why24CCZPhase (retained : Semantics.Qubit.Bitstring (Fin 3)) : ZMod 2 :=
  let word := PauliSymplectic.bitstringWordEquiv (Fin 3) retained
  word 0 * word 1 * word 2

/-- The literal Appendix gate-list phase after fixing one measurement outcome. -/
def why24AppendixReverseSourcePhase
    (outcome : Why24AppendixReverseOutcome)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) : ZMod 2 :=
  why24AppendixWordPhaseList why24AppendixGateList
    (PauliSymplectic.bitstringWordEquiv (Fin 10)
      (why24AppendixReverseRecombine retained outcome))

/-- The diagonal correction repeats the literal Appendix phase and restores
only the retained `CCZ` phase.  Once the seven outcome bits are fixed, every
listed term other than `CCZ_{0,1,2}` has retained degree at most two, exactly
matching the source's `Z`/`CZ` correction description. -/
def why24AppendixReverseCorrectionPhase
    (outcome : Why24AppendixReverseOutcome)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) : ZMod 2 :=
  why24AppendixReverseSourcePhase outcome retained + why24CCZPhase retained

/-- The correction cancels the actual literal source phase and leaves exactly
the retained `CCZ` phase. -/
theorem why24AppendixReverseCorrectionPhase_add_source
    (outcome : Why24AppendixReverseOutcome)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseCorrectionPhase outcome retained +
        why24AppendixReverseSourcePhase outcome retained =
      why24CCZPhase retained := by
  rw [why24AppendixReverseCorrectionPhase]
  let source := why24AppendixReverseSourcePhase outcome retained
  let target := why24CCZPhase retained
  change (source + target) + source = target
  calc
    (source + target) + source = target + (source + source) := by
      rw [add_assoc, add_comm target source, ← add_assoc,
        add_comm (source + source) target]
    _ = target := by
      rw [CharTwo.add_self_eq_zero, add_zero]

end QEC.Coding
