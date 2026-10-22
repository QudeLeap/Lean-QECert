import QEC.Semantics.Core.Subsystem
/-!
# Finite operational erasure distance

This module definitionally derives a local finite operational-erasure-distance
convention from the least size of a subsystem whose concrete erasure channel is
not recoverable. The no-failure case is represented by one more than the
number of coordinates, so the convention remains a natural number for every
finite register.

This convention claims no relation to standard quantum-code, stabilizer, CSS,
or algebraic distance. It does not prove any implication from
`SemanticStabilizerDistance`, CSS distance, or algebraic distance to erasure
correction.
-/

noncomputable section

namespace QEC
namespace Locality

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A coordinate-cardinality at which a concrete subsystem erasure is not recoverable. -/
def FiniteOperationalErasureFailureAt
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι)) (n : Nat) : Prop :=
  ∃ S : Semantics.FiniteSubsystem ι,
    S.selected.card = n ∧ ¬ S.ErasureRecoverableFromRegister C

/--
The local finite operational-erasure-distance convention: the least cardinality
of a nonrecoverable erasure, or one past the full coordinate count when none
exists.
-/
noncomputable def finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι)) : Nat := by
  classical
  exact if h : ∃ n, FiniteOperationalErasureFailureAt C n then Nat.find h
    else Fintype.card ι + 1

/-- An extant erasure failure attains the local operational-erasure-distance convention. -/
theorem leastFailure_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (hFailure : ∃ n, FiniteOperationalErasureFailureAt C n) :
    FiniteOperationalErasureFailureAt C (finiteOperationalErasureDistance C) ∧
      ∀ n, FiniteOperationalErasureFailureAt C n → finiteOperationalErasureDistance C ≤ n := by
  classical
  rw [finiteOperationalErasureDistance, dif_pos hFailure]
  exact ⟨Nat.find_spec hFailure, fun _ h => Nat.find_min' hFailure h⟩

/-- With no erasure failure, the local convention is capped at `|ι| + 1`. -/
theorem noErasureFailure_eq_total_succ_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (hRecoverable : ∀ S : Semantics.FiniteSubsystem ι, S.ErasureRecoverableFromRegister C) :
    finiteOperationalErasureDistance C = Fintype.card ι + 1 := by
  classical
  have hNoFailure : ¬ ∃ n, FiniteOperationalErasureFailureAt C n := by
    rintro ⟨_, S, _, hS⟩
    exact hS (hRecoverable S)
  simp [finiteOperationalErasureDistance, hNoFailure]

/-- A nonrecoverable subsystem has cardinality at least the local convention. -/
theorem nonrecoverableCardLowerBound_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (S : Semantics.FiniteSubsystem ι)
    (hS : ¬ S.ErasureRecoverableFromRegister C) :
    finiteOperationalErasureDistance C ≤ S.selected.card := by
  classical
  have hFailure : ∃ n, FiniteOperationalErasureFailureAt C n :=
    ⟨S.selected.card, S, rfl, hS⟩
  rw [finiteOperationalErasureDistance, dif_pos hFailure]
  exact Nat.find_min' hFailure ⟨S, rfl, hS⟩

/-- Every subsystem smaller than the local convention is recoverable after its concrete erasure. -/
theorem erasureRecoverableFromRegister_of_card_lt_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (S : Semantics.FiniteSubsystem ι)
    (hCard : S.selected.card < finiteOperationalErasureDistance C) :
    S.ErasureRecoverableFromRegister C := by
  classical
  by_contra hS
  exact (Nat.not_le_of_lt hCard)
    (nonrecoverableCardLowerBound_finiteOperationalErasureDistance C S hS)

/--
A subsystem smaller than the local convention has a concrete CPTP recovery
channel from its finite-subsystem erasure channel.
-/
theorem exists_erasureRecoveryChannel_of_card_lt_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (S : Semantics.FiniteSubsystem ι) {d : Nat}
    (hDistance : d = finiteOperationalErasureDistance C)
    (hCard : S.selected.card < d) :
    ∃ recovery : Semantics.QuantumChannel S.complementSystem
        (Semantics.Qubit.QubitRegister ι),
      Semantics.Correctable (Semantics.Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  subst d
  exact (S.erasureRecoverableFromRegister_iff_exists_correctable C).1
    (erasureRecoverableFromRegister_of_card_lt_finiteOperationalErasureDistance C S hCard)

end Locality
end QEC
