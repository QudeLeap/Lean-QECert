import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Stack growth of finite-control Boolean Turing machines

Count pushes in the actual TM2 instruction tree. Every actual step increases total stack
length by at most the finite program's maximum count; induction yields the corresponding
bound for every counted execution. The bound is derived from syntax and execution rather
than supplied as a machine field.
-/

namespace QEC.Coding.BitTuring
open Turing
open scoped BigOperators

/-- Maximum number of pushes along one branch of an actual instruction tree. -/
def pushes {K Λ σ : Type} : TM2.Stmt (fun _ : K => Bool) Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

/-- Total Boolean stack length, summed over the finite stack set. -/
def stackSize {K : Type} [Fintype K] (tapes : K → List Bool) : ℕ :=
  ∑ k, (tapes k).length

/-- Exact length balance when replacing one stack. -/
theorem stackSize_update {K : Type} [Fintype K] [DecidableEq K]
    (tapes : K → List Bool) (k : K) (value : List Bool) :
    stackSize (Function.update tapes k value) + (tapes k).length =
      stackSize tapes + value.length := by
  have hu : (fun j => (Function.update tapes k value j).length) =
      Function.update (fun j => (tapes j).length) k value.length := by
    funext j
    by_cases hj : j = k <;> simp [hj]
  simp only [stackSize, hu]
  rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add Finset.univ (fun j => (tapes j).length) (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

/-- One Boolean push increases total stack length by exactly one. -/
theorem stackSize_push {K : Type} [Fintype K] [DecidableEq K]
    (tapes : K → List Bool) (k : K) (bit : Bool) :
    stackSize (Function.update tapes k (bit :: tapes k)) = stackSize tapes + 1 := by
  have h := stackSize_update tapes k (bit :: tapes k)
  simp only [List.length_cons] at h
  omega

/-- One pop cannot increase total stack length. -/
theorem stackSize_pop {K : Type} [Fintype K] [DecidableEq K]
    (tapes : K → List Bool) (k : K) :
    stackSize (Function.update tapes k (tapes k).tail) ≤ stackSize tapes := by
  have h := stackSize_update tapes k (tapes k).tail
  have ht : (tapes k).tail.length ≤ (tapes k).length := by simp only [List.length_tail]; omega
  omega

/-- Instruction induction bounds growth by the actual push count. -/
theorem stepAux_stackSize_le {K Λ σ : Type} [Fintype K] [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (tapes : K → List Bool) :
    stackSize (TM2.stepAux q v tapes).stk ≤ stackSize tapes + pushes q := by
  induction q generalizing v tapes with
  | push k f q ih =>
      simpa only [TM2.stepAux, pushes, stackSize_push, Nat.add_assoc, Nat.add_comm 1]
        using ih v (Function.update tapes k (f v :: tapes k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
      exact (ih _ _).trans (Nat.add_le_add_right (stackSize_pop tapes k) _)
  | load f q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases h : f v
      · simpa [TM2.stepAux, h, pushes] using (ih₂ v tapes).trans
          (Nat.add_le_add_left (Nat.le_max_right (pushes q₁) (pushes q₂)) _)
      · simpa [TM2.stepAux, h, pushes] using (ih₁ v tapes).trans
          (Nat.add_le_add_left (Nat.le_max_left (pushes q₁) (pushes q₂)) _)
  | goto f => exact le_refl _
  | halt => exact le_refl _

/-- Maximum syntactic push count over the finite program labels. -/
def programPushes {K Λ σ : Type} [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : ℕ :=
  Finset.univ.sup (fun l => pushes (M l))

/-- Every instruction tree is bounded by the finite program maximum. -/
theorem pushes_le_programPushes {K Λ σ : Type} [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (l : Λ) :
    pushes (M l) ≤ programPushes M :=
  Finset.le_sup (f := fun l => pushes (M l)) (Finset.mem_univ l)

/-- One actual machine transition satisfies the syntactic growth bound. -/
theorem step_stackSize_le {K Λ σ : Type} [Fintype K] [DecidableEq K] [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (c c' : TM2.Cfg (fun _ : K => Bool) Λ σ) (hstep : TM2.step M c = some c') :
    stackSize c'.stk ≤ stackSize c.stk + programPushes M := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at hstep
  | some l =>
      have hc : TM2.stepAux (M l) v S = c' := Option.some.inj hstep
      rw [← hc]
      exact (stepAux_stackSize_le _ _ _).trans
        (Nat.add_le_add_left (pushes_le_programPushes M l) _)

/-- Counted actual executions satisfy the accumulated stack-growth bound. -/
theorem iterate_stackSize_le {K Λ σ : Type} [Fintype K] [DecidableEq K] [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (n : ℕ)
    (c c' : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (hRun : (fun x => x.bind (TM2.step M))^[n] (some c) = some c') :
    stackSize c'.stk ≤ stackSize c.stk + n * programPushes M := by
  induction n generalizing c with
  | zero =>
      have h : c = c' := Option.some.inj hRun
      subst c'
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hRun
      cases hStep : TM2.step M c with
      | none =>
          simp only [Option.bind_some, hStep] at hRun
          have hn : (fun x => x.bind (TM2.step M))^[n] none = none := by
            exact Function.iterate_fixed (f := fun x : Option (TM2.Cfg (fun _ : K => Bool) Λ σ) => x.bind (TM2.step M)) rfl n
          rw [hn] at hRun
          cases hRun
      | some c₁ =>
          simp only [Option.bind_some, hStep] at hRun
          have hi := ih c₁ hRun
          have hs := step_stackSize_le M c c₁ hStep
          calc
            stackSize c'.stk ≤ stackSize c₁.stk + n * programPushes M := hi
            _ ≤ stackSize c.stk + programPushes M + n * programPushes M := Nat.add_le_add_right hs _
            _ = stackSize c.stk + (n + 1) * programPushes M := by ring

end QEC.Coding.BitTuring
