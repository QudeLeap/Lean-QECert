import QEC.Coding.BitTuring.UnaryResiduePrime
import QEC.Coding.ExpanderCodes.LPSEffectivePrime

/-!
# Actual LPS least-prime program and carrier-sensitive runtime

The fixed-modulus finite Boolean program executes the original candidate test
`max B (4*p) < q`, primality, and residue one. Dirichlet gives an eligible endpoint;
`Nat.find` minimality proves every earlier candidate fails. These mathematical
proofs construct complete execution of the real program, rather than populating
an oracle or an assumed output/time/termination field.

For every prime p and unary bound B, the program returns precisely the existing
`lpsLeastPrimeAbove hp B`. For the actual source-compatible LPS family, the
proved inequality `q <= 2*card(PSL)` transports its explicit quintic selected-q
budget to a polynomial in the actual output carrier size. This is not a
polynomial-in-B claim, binary-input bound, full sparse CSS emission certificate,
or unconditional spectral/main-theorem result. The original sequence and
arbitrary finite-field public scope are preserved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Turing StateTransition
open QEC.Coding.BitTuring
open QEC.Coding.BitTuring.UnaryArithmetic

/-- A finite Boolean program for the original least-prime sequence at fixed p. -/
def lpsPrimeMachine {p : ℕ} (hp : p.Prime) : Machine :=
  ResiduePrime.fullMachine (4*p) (Nat.mul_pos (by norm_num) hp.pos)

/-- Dirichlet and least-candidate minimality justify the actual complete run, not runtime callbacks. -/
noncomputable def lpsPrimeMachineExec {p : ℕ} (hp : p.Prime) (B : ℕ) :
    EvalsToInTime (TM2.step (lpsPrimeMachine hp).program) ((lpsPrimeMachine hp).init (unary B))
      (some ((lpsPrimeMachine hp).halt (unary (lpsLeastPrimeAbove hp B))))
      (ResiduePrime.fullTime.eval (lpsLeastPrimeAbove hp B)) := by
  have h := lpsLeastPrimeAbove_spec hp B
  exact ResiduePrime.fullExec (4*p) (Nat.mul_pos (by norm_num) hp.pos) B _ h.1 h.2
    (fun n hB hn he => Nat.find_min (exists_lpsPrimeCandidate hp B) hn ⟨hB,he⟩)

open scoped MatrixGroups

/-- Genuine complete prime-selection execution has polynomial cost in the actual PSL carrier size. -/
noncomputable def lpsPrimeMachineBlockExec {p : ℕ} (hp : p.Prime) (hp4 : p%4=1) (B : ℕ) :
    EvalsToInTime (TM2.step (lpsPrimeMachine hp).program) ((lpsPrimeMachine hp).init (unary B))
      (some ((lpsPrimeMachine hp).halt (unary (lpsEffectiveResiduePrimeAt hp hp4 B).q)))
      (ResiduePrime.fullTime.eval (2*Fintype.card PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q))) := by
  have h := lpsPrimeMachineExec hp B
  rw [← lpsEffectiveResiduePrimeAt_q hp hp4 B] at h
  refine {h with steps_le_m := h.steps_le_m.trans ?_}
  exact Composition.polynomial_eval_monotone ResiduePrime.fullTime
    (lpsEffectiveResiduePrimeAt hp hp4 B).q_le_two_mul_card_psl

/-- Standard output-in-time certificate for the original family prime at the proved carrier budget. -/
noncomputable def lpsPrimeMachineOutputsInTime {p : ℕ} (hp : p.Prime) (hp4 : p%4=1) (B : ℕ) :
    TM2OutputsInTime (lpsPrimeMachine hp).toFinTM2 (unary B)
      (some (unary (lpsEffectiveResiduePrimeAt hp hp4 B).q))
      (ResiduePrime.fullTime.eval (2*Fintype.card PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q))) :=
  Machine.outputsInTime _ _ _ _ (lpsPrimeMachineBlockExec hp hp4 B)

end QEC.Coding.TannerLiftedProduct
