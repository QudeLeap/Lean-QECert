import QEC.Coding.BitTuring.StackGrowth
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Finite-control Boolean Turing-machine composition

Construct disjoint finite controls and stacks for two actual TM2 programs. Redirect the first
halt through two reverse-copy loops, then start the second program with exactly the first
output. Prove instruction/step/run simulation, exact transfer cost, full output semantics and
polynomial runtime closure using the stack-growth theorem.

Time counts actual Mathlib TM2 label steps. A fixed finite program executes a bounded
instruction tree in each label step; variables, stack alphabets and control are all finite.
The polynomials describe mathematical bounds and do not participate in machine execution.
This is internal construction machinery, not a certificate for an arbitrary numeric generator
or the complete explicit PK22 family.
-/

namespace QEC.Coding.BitTuring
open Turing
open StateTransition

/-- Two finite-control loops reverse through a buffer and restore the input order. -/
def copyProgram : Bool → TM2.Stmt (fun _ : Fin 3 => Bool) Bool (Option Bool)
  | true => .pop 0 (fun _ head => head)
      (.branch Option.isSome
        (.push 1 (fun v => v.getD false) (.goto fun _ => true))
        (.goto fun _ => false))
  | false => .pop 1 (fun _ head => head)
      (.branch Option.isSome
        (.push 2 (fun v => v.getD false) (.goto fun _ => false)) .halt)

/-- Copy configuration with source, buffer and destination Boolean stacks. -/
def copyCfg (phase : Bool) (source buffer output : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Bool (Option Bool) :=
  ⟨some phase, v, ![source,buffer,output]⟩

/-- Finished copy configuration with the source and buffer drained. -/
def copyHalt (output : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Bool (Option Bool) :=
  ⟨none,none,![[],[],output]⟩

/-- The first loop drains one source bit into the buffer. -/
theorem copyStep_source_cons (x : Bool) (xs b d : List Bool) (v : Option Bool) :
    TM2.step copyProgram (copyCfg true (x :: xs) b d v) =
      some (copyCfg true xs (x :: b) d (some x)) := by
  simp [TM2.step, copyCfg, copyProgram, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp

/-- An empty source switches to the second loop in one actual step. -/
theorem copyStep_source_nil (b d : List Bool) (v : Option Bool) :
    TM2.step copyProgram (copyCfg true [] b d v) =
      some (copyCfg false [] b d none) := by
  simp [TM2.step, copyCfg, copyProgram, TM2.stepAux, TM2.Cfg.mk.injEq]

/-- The second loop drains one buffer bit into the destination. -/
theorem copyStep_buffer_cons (x : Bool) (xs d : List Bool) (v : Option Bool) :
    TM2.step copyProgram (copyCfg false [] (x :: xs) d v) =
      some (copyCfg false [] xs (x :: d) (some x)) := by
  simp [TM2.step, copyCfg, copyProgram, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp

/-- An empty buffer reaches the genuine copy halt in one actual step. -/
theorem copyStep_buffer_nil (d : List Bool) (v : Option Bool) :
    TM2.step copyProgram (copyCfg false [] [] d v) = some (copyHalt d) := by
  simp [TM2.step, copyCfg, copyHalt, copyProgram, TM2.stepAux, TM2.Cfg.mk.injEq]

/-- The first loop reverses the source into the buffer in length plus one steps. -/
theorem copyRun_source (w b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step copyProgram))^[w.length + 1]
        (some (copyCfg true w b d v)) =
      some (copyCfg false [] (w.reverse ++ b) d none) := by
  induction w generalizing b v with
  | nil => simp [copyStep_source_nil]
  | cons x xs ih =>
      rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
      simp only [Option.bind_some, copyStep_source_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (x :: b) (some x)

/-- The second loop reverses the buffer into the destination in length plus one steps. -/
theorem copyRun_buffer (w d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step copyProgram))^[w.length + 1]
        (some (copyCfg false [] w d v)) = some (copyHalt (w.reverse ++ d)) := by
  induction w generalizing d v with
  | nil => simp [copyStep_buffer_nil]
  | cons x xs ih =>
      rw [List.length_cons, Nat.add_right_comm, Function.iterate_succ_apply]
      simp only [Option.bind_some, copyStep_buffer_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (x :: d) (some x)

/-- The actual two-loop program transfers a whole bit string in twice its length plus two steps. -/
theorem copyRun (w : List Bool) :
    (fun c => c.bind (TM2.step copyProgram))^[2 * w.length + 2]
      (some (copyCfg true w [] [] none)) = some (copyHalt w) := by
  have ht : 2 * w.length + 2 = (w.reverse.length + 1) + (w.length + 1) := by simp; omega
  rw [ht, Function.iterate_add_apply, copyRun_source]
  simpa using copyRun_buffer w.reverse [] none

section Lift
variable {K K' Λ Λ' σ σ' : Type}

/-- Embed actual Boolean instructions into larger finite controls, redirecting halt if requested. -/
def liftStatement (stack : K → K') (label : Λ → Λ') (get : σ' → σ)
    (put : σ' → σ → σ') (haltLabel : Option Λ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K' => Bool) Λ' σ'
  | .push k f q => .push (stack k) (fun v => f (get v))
      (liftStatement stack label get put haltLabel q)
  | .peek k f q => .peek (stack k) (fun v h => put v (f (get v) h))
      (liftStatement stack label get put haltLabel q)
  | .pop k f q => .pop (stack k) (fun v h => put v (f (get v) h))
      (liftStatement stack label get put haltLabel q)
  | .load f q => .load (fun v => put v (f (get v)))
      (liftStatement stack label get put haltLabel q)
  | .branch f q₁ q₂ => .branch (fun v => f (get v))
      (liftStatement stack label get put haltLabel q₁)
      (liftStatement stack label get put haltLabel q₂)
  | .goto f => .goto (fun v => label (f (get v)))
  | .halt => haltLabel.elim .halt (fun l => .goto fun _ => l)

/-- Embed labels, variables and tapes, with the same explicit halt redirection. -/
def liftCfg (label : Λ → Λ') (embedVar : σ → σ')
    (embedTapes : (K → List Bool) → K' → List Bool) (haltLabel : Option Λ')
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K' => Bool) Λ' σ' :=
  ⟨c.l.elim haltLabel (fun l => some (label l)), embedVar c.var, embedTapes c.stk⟩

variable [DecidableEq K] [DecidableEq K']

/-- Instruction induction proves that lifting preserves actual execution. -/
theorem stepAux_liftStatement (stack : K → K') (label : Λ → Λ')
    (get : σ' → σ) (put : σ' → σ → σ') (haltLabel : Option Λ')
    (embedVar : σ → σ') (embedTapes : (K → List Bool) → K' → List Bool)
    (hget : ∀ v, get (embedVar v) = v)
    (hput : ∀ v w, put (embedVar v) w = embedVar w)
    (hread : ∀ S k, embedTapes S (stack k) = S k)
    (hupdate : ∀ S k w, Function.update (embedTapes S) (stack k) w =
      embedTapes (Function.update S k w))
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (S : K → List Bool) :
    TM2.stepAux (liftStatement stack label get put haltLabel q) (embedVar v)
        (embedTapes S) =
      liftCfg label embedVar embedTapes haltLabel (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simpa [liftStatement, hget, hread, hupdate] using ih v (Function.update S k (f v :: S k))
  | peek k f q ih => simpa [liftStatement, hget, hput, hread] using ih (f v (S k).head?) S
  | pop k f q ih => simpa [liftStatement, hget, hput, hread, hupdate] using ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => simpa [liftStatement, hget, hput] using ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases h : f v
      · simpa [liftStatement, hget, h] using ih₂ v S
      · simpa [liftStatement, hget, h] using ih₁ v S
  | goto f => simp [liftStatement, liftCfg, hget]
  | halt => cases haltLabel <;> rfl

end Lift

/-- A step simulation preserves every successful counted run, including its step count. -/
theorem iterate_lift {C D : Type} (f : C → Option C) (g : D → Option D) (embed : C → D)
    (hstep : ∀ c c', f c = some c' → g (embed c) = some (embed c'))
    (n : ℕ) (c c' : C) (hRun : (fun x => x.bind f)^[n] (some c) = some c') :
    (fun x => x.bind g)^[n] (some (embed c)) = some (embed c') := by
  induction n generalizing c with
  | zero => simpa using congrArg (Option.map embed) hRun
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hRun ⊢
      cases hs : f c with
      | none =>
          simp only [Option.bind_some, hs] at hRun
          have hn : (fun x => x.bind f)^[n] none = none := Function.iterate_fixed rfl n
          rw [hn] at hRun
          cases hRun
      | some c₁ =>
          simp only [Option.bind_some, hs] at hRun
          simp only [Option.bind_some, hstep c c₁ hs]
          exact ih c₁ hRun

/-- An actual Boolean TM2 with finite stacks, labels and variables; no target or cost field. -/
structure Machine where
  K : Type
  [kDecidableEq : DecidableEq K]
  [kFintype : Fintype K]
  (input output : K)
  Λ : Type
  [labelFintype : Fintype Λ]
  main : Λ
  σ : Type
  [varFintype : Fintype σ]
  initial : σ
  program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

attribute [instance] Machine.kDecidableEq Machine.kFintype Machine.labelFintype Machine.varFintype

namespace Machine

/-- View the Boolean program as Mathlib's finite TM2 without changing its instructions. -/
def toFinTM2 (M : Machine) : FinTM2 where
  K := M.K
  k₀ := M.input
  k₁ := M.output
  Γ := fun _ => Bool
  Λ := M.Λ
  main := M.main
  σ := M.σ
  initialState := M.initial
  m := M.program

/-- Actual configurations of the finite Boolean program. -/
abbrev Cfg (M : Machine) := TM2.Cfg (fun _ : M.K => Bool) M.Λ M.σ

/-- Initial finite-control configuration with only the input stack populated. -/
def init (M : Machine) (input : List Bool) : M.Cfg :=
  ⟨some M.main, M.initial, Function.update (fun _ => []) M.input input⟩

/-- Exact output configuration with reset variables and only the output stack populated. -/
def halt (M : Machine) (output : List Bool) : M.Cfg :=
  ⟨none, M.initial, Function.update (fun _ => []) M.output output⟩

/-- The Boolean initial configuration equals Mathlib's standard initial configuration. -/
theorem init_toFinTM2 (M : Machine) (w : List Bool) : initList M.toFinTM2 w = M.init w := by
  simp only [initList, toFinTM2, init]
  congr 1
  funext k
  by_cases h : k = M.input
  · subst k; rfl
  · simp [Function.update, h]

/-- The Boolean final configuration equals Mathlib's standard output configuration. -/
theorem halt_toFinTM2 (M : Machine) (w : List Bool) : haltList M.toFinTM2 w = M.halt w := by
  simp only [haltList, toFinTM2, halt]
  congr 1
  funext k
  by_cases h : k = M.output
  · subst k; rfl
  · simp [Function.update, h]

/-- Convert a real Boolean execution to Mathlib's standard finite-machine output certificate. -/
def outputsInTime (M : Machine) (x y : List Bool) (a : ℕ)
    (h : EvalsToInTime (TM2.step M.program) (M.init x) (some (M.halt y)) a) :
    TM2OutputsInTime M.toFinTM2 x (some y) a := by
  change EvalsToInTime (TM2.step M.program) (initList M.toFinTM2 x)
    (some (haltList M.toFinTM2 y)) a
  rw [init_toFinTM2, halt_toFinTM2]
  exact h

/-- A configuration containing one populated stack has exactly that stack's length. -/
theorem stackSize_single (M : Machine) (k : M.K) (w : List Bool) :
    stackSize (Function.update (fun _ : M.K => []) k w) = w.length := by
  have h := stackSize_update (fun _ : M.K => []) k w
  simpa [stackSize] using h

/-- Actual execution and the syntactic growth bound control output length. -/
theorem output_length_le (M : Machine) (x y : List Bool) (a : ℕ)
    (h : EvalsToInTime (TM2.step M.program) (M.init x) (some (M.halt y)) a) :
    y.length ≤ x.length + a * programPushes M.program := by
  have hh := iterate_stackSize_le M.program h.steps (M.init x) (M.halt y) h.evals_in_steps
  simp only [Machine.init, Machine.halt, stackSize_single] at hh
  exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Machine

namespace Composition
variable (A B : Machine)
/-- Disjoint first/second stacks plus a single transfer buffer. -/
abbrev Stack := A.K ⊕ (Unit ⊕ B.K)
/-- Disjoint first/second labels plus two transfer phases. -/
abbrev Label := A.Λ ⊕ (Bool ⊕ B.Λ)
/-- Two finite variable sets plus the last transferred Boolean head. -/
abbrev Var := A.σ × B.σ × Option Bool

/-- First-program stacks embedded with the other component and buffer empty. -/
def tapes₁ (S : A.K → List Bool) : Stack A B → List Bool
  | .inl k => S k
  | .inr _ => []

/-- Second-program stacks embedded with the first component and buffer empty. -/
def tapes₂ (S : B.K → List Bool) : Stack A B → List Bool
  | .inr (.inr k) => S k
  | _ => []

/-- Embed the first run, redirecting its halt to the first transfer phase. -/
def embed₁ : A.Cfg → TM2.Cfg (fun _ : Stack A B => Bool) (Label A B) (Var A B) :=
  liftCfg Sum.inl (fun v => (v, B.initial, none)) (tapes₁ A B) (some (.inr (.inl true)))

/-- Embed the second run, preserving its genuine halt. -/
def embed₂ : B.Cfg → TM2.Cfg (fun _ : Stack A B => Bool) (Label A B) (Var A B) :=
  liftCfg (fun l => .inr (.inr l)) (fun v => (A.initial, v, none)) (tapes₂ A B) none

/-- A first-component stack update commutes with its disjoint embedding. -/
theorem tapes₁_update (S : A.K → List Bool) (k : A.K) (w : List Bool) :
    Function.update (tapes₁ A B S) (.inl k) w = tapes₁ A B (Function.update S k w) := by
  funext j
  cases j with
  | inl j => by_cases h : j = k <;> simp [tapes₁, h]
  | inr j => simp [tapes₁]

/-- A second-component stack update commutes with its disjoint embedding. -/
theorem tapes₂_update (S : B.K → List Bool) (k : B.K) (w : List Bool) :
    Function.update (tapes₂ A B S) (.inr (.inr k)) w = tapes₂ A B (Function.update S k w) := by
  funext j
  cases j with
  | inl j => simp [tapes₂]
  | inr j => cases j with
    | inl j => simp [tapes₂]
    | inr j => by_cases h : j = k <;> simp [tapes₂, h]

/-- Map the three copy stacks to first output, buffer and second input. -/
def copyStack (k : Fin 3) : Stack A B :=
  if k = 0 then .inl A.output else if k = 1 then .inr (.inl ()) else .inr (.inr B.input)

/-- Embed the three copy stacks with every other component stack empty. -/
def copyTapes (S : Fin 3 → List Bool) : Stack A B → List Bool
  | .inl k => if k = A.output then S 0 else []
  | .inr (.inl _) => S 1
  | .inr (.inr k) => if k = B.input then S 2 else []

/-- Embed the real copy program, redirecting its halt to the second entry label. -/
def embedCopy : TM2.Cfg (fun _ : Fin 3 => Bool) Bool (Option Bool) →
    TM2.Cfg (fun _ : Stack A B => Bool) (Label A B) (Var A B) :=
  liftCfg (fun phase => .inr (.inl phase)) (fun v => (A.initial, B.initial, v))
    (copyTapes A B) (some (.inr (.inr B.main)))

/-- Every embedded copy stack reads exactly the corresponding original bit string. -/
theorem copyTapes_read (S : Fin 3 → List Bool) (k : Fin 3) :
    copyTapes A B S (copyStack A B k) = S k := by
  fin_cases k <;> simp [copyStack, copyTapes]

/-- A copy-stack update commutes with the disjoint three-stack embedding. -/
theorem copyTapes_update (S : Fin 3 → List Bool) (k : Fin 3) (w : List Bool) :
    Function.update (copyTapes A B S) (copyStack A B k) w =
      copyTapes A B (Function.update S k w) := by
  fin_cases k <;> funext j
  all_goals
    cases j with
    | inl j => by_cases h : j = A.output <;> simp [copyStack, copyTapes, h]
    | inr j => cases j with
      | inl j => cases j; simp [copyStack, copyTapes]
      | inr j => by_cases h : j = B.input <;> simp [copyStack, copyTapes, h]

/-- Actual first program, two-pass transfer, and second program on disjoint finite controls. -/
def program : Label A B →
    TM2.Stmt (fun _ : Stack A B => Bool) (Label A B) (Var A B)
  | .inl l => liftStatement Sum.inl Sum.inl Prod.fst
      (fun v w => (w, v.2)) (some (.inr (.inl true))) (A.program l)
  | .inr (.inr l) => liftStatement (fun k => .inr (.inr k))
      (fun l => .inr (.inr l)) (fun v => v.2.1)
      (fun v w => (v.1, w, v.2.2)) none (B.program l)
  | .inr (.inl phase) => liftStatement
      (copyStack A B)
      (fun phase => .inr (.inl phase)) (fun v => v.2.2)
      (fun v w => (v.1, v.2.1, w)) (some (.inr (.inr B.main))) (copyProgram phase)

/-- Each lifted first-program instruction has exactly the original semantics. -/
theorem stepAux₁ (l : A.Λ) (v : A.σ) (S : A.K → List Bool) :
    TM2.stepAux (program A B (.inl l)) (v, B.initial, none) (tapes₁ A B S) =
      embed₁ A B (TM2.stepAux (A.program l) v S) :=
  stepAux_liftStatement (K := A.K) (K' := Stack A B) (Λ := A.Λ) (Λ' := Label A B)
    (σ := A.σ) (σ' := Var A B) Sum.inl Sum.inl Prod.fst (fun v w => (w, v.2))
    (some (.inr (.inl true))) (fun v => (v, B.initial, none)) (tapes₁ A B)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (tapes₁_update A B) (A.program l) v S

/-- Each lifted second-program instruction has exactly the original semantics. -/
theorem stepAux₂ (l : B.Λ) (v : B.σ) (S : B.K → List Bool) :
    TM2.stepAux (program A B (.inr (.inr l))) (A.initial, v, none) (tapes₂ A B S) =
      embed₂ A B (TM2.stepAux (B.program l) v S) :=
  stepAux_liftStatement (K := B.K) (K' := Stack A B) (Λ := B.Λ) (Λ' := Label A B)
    (σ := B.σ) (σ' := Var A B) (fun k => .inr (.inr k)) (fun l => .inr (.inr l))
    (fun v => v.2.1) (fun v w => (v.1, w, v.2.2)) none
    (fun v => (A.initial, v, none)) (tapes₂ A B)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (tapes₂_update A B) (B.program l) v S

/-- Each lifted copy instruction has exactly the original semantics. -/
theorem stepAuxCopy (phase : Bool) (v : Option Bool) (S : Fin 3 → List Bool) :
    TM2.stepAux (program A B (.inr (.inl phase))) (A.initial, B.initial, v) (copyTapes A B S) =
      embedCopy A B (TM2.stepAux (copyProgram phase) v S) :=
  stepAux_liftStatement (K := Fin 3) (K' := Stack A B) (Λ := Bool) (Λ' := Label A B)
    (σ := Option Bool) (σ' := Var A B) (copyStack A B) (fun phase => .inr (.inl phase))
    (fun v => v.2.2) (fun v w => (v.1, v.2.1, w)) (some (.inr (.inr B.main)))
    (fun v => (A.initial, B.initial, v)) (copyTapes A B)
    (fun _ => rfl) (fun _ _ => rfl) (copyTapes_read A B) (copyTapes_update A B) (copyProgram phase) v S

/-- Every successful first-program transition is one actual combined transition. -/
theorem step₁ (c c' : A.Cfg) (h : TM2.step A.program c = some c') :
    TM2.step (program A B) (embed₁ A B c) = some (embed₁ A B c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (A.program l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAux₁ A B l v S)

/-- Every successful second-program transition is one actual combined transition. -/
theorem step₂ (c c' : B.Cfg) (h : TM2.step B.program c = some c') :
    TM2.step (program A B) (embed₂ A B c) = some (embed₂ A B c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (B.program l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAux₂ A B l v S)

/-- Every successful copy transition is one actual combined transition. -/
theorem stepCopy (c c' : TM2.Cfg (fun _ : Fin 3 => Bool) Bool (Option Bool))
    (h : TM2.step copyProgram c = some c') :
    TM2.step (program A B) (embedCopy A B c) = some (embedCopy A B c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (copyProgram l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAuxCopy A B l v S)

/-- The first exact output configuration is the copy entry configuration. -/
theorem embedCopy_start (w : List Bool) :
    embedCopy A B (copyCfg true w [] [] none) = embed₁ A B (A.halt w) := by
  simp only [embedCopy, embed₁, liftCfg, copyCfg, Machine.halt, Option.elim_some, Option.elim_none]
  congr 1
  funext j
  cases j with
  | inl j => by_cases h : j = A.output <;> simp [copyTapes, tapes₁, h]
  | inr j => cases j with
    | inl j => simp [copyTapes, tapes₁]
    | inr j => simp [copyTapes, tapes₁]

/-- The copy output configuration is exactly the second input configuration. -/
theorem embedCopy_end (w : List Bool) :
    embedCopy A B (copyHalt w) = embed₂ A B (B.init w) := by
  simp only [embedCopy, embed₂, liftCfg, copyHalt, Machine.init, Option.elim_some, Option.elim_none]
  congr 1
  funext j
  cases j with
  | inl j => simp [copyTapes, tapes₂]
  | inr j => cases j with
    | inl j => simp [copyTapes, tapes₂]
    | inr j => by_cases h : j = B.input <;> simp [copyTapes, tapes₂, h]

/-- The constructed program transfers the intermediate output in exactly twice its length plus two steps. -/
theorem transfer (w : List Bool) :
    (fun c => c.bind (TM2.step (program A B)))^[2 * w.length + 2]
      (some (embed₁ A B (A.halt w))) = some (embed₂ A B (B.init w)) := by
  simpa only [embedCopy_start, embedCopy_end] using
    iterate_lift (TM2.step copyProgram) (TM2.step (program A B)) (embedCopy A B)
      (stepCopy A B) _ _ _ (copyRun w)

/-- Construct the combined finite Boolean machine from actual program syntax. -/
def machine : Machine where
  K := Stack A B
  input := .inl A.input
  output := .inr (.inr B.output)
  Λ := Label A B
  main := .inl A.main
  σ := Var A B
  initial := (A.initial, B.initial, none)
  program := program A B

/-- The embedded first input is exactly the combined input configuration. -/
theorem embed₁_init (w : List Bool) :
    embed₁ A B (A.init w) = (machine A B).init w := by
  simp only [embed₁, liftCfg, Machine.init, machine, Option.elim_some]
  congr 1
  funext j
  cases j with
  | inl j => by_cases h : j = A.input <;> simp [tapes₁, Function.update, h]
  | inr j => simp [tapes₁, Function.update]

/-- The embedded second output is exactly the combined output configuration. -/
theorem embed₂_halt (w : List Bool) :
    embed₂ A B (B.halt w) = (machine A B).halt w := by
  simp only [embed₂, liftCfg, Machine.halt, machine, Option.elim_none]
  congr 1
  funext j
  cases j with
  | inl j => simp [tapes₂, Function.update]
  | inr j => cases j with
    | inl j => simp [tapes₂, Function.update]
    | inr j => by_cases h : j = B.output <;> simp [tapes₂, Function.update, h]

-- The machine is constructed first; this theorem certifies its actual execution.
/-- Certify actual combined output and the sum of both execution budgets plus transfer steps. -/
def executes (x y z : List Bool) (a b : ℕ)
    (hA : EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt y)) a)
    (hB : EvalsToInTime (TM2.step B.program) (B.init y) (some (B.halt z)) b) :
    EvalsToInTime (TM2.step (machine A B).program)
      ((machine A B).init x) (some ((machine A B).halt z))
      (b + (2 * y.length + 2) + a) := by
  have hRun :
      (fun c : Option (TM2.Cfg (fun _ : Stack A B => Bool) (Label A B) (Var A B)) =>
        c.bind (TM2.step (program A B)))^[hB.steps + (2 * y.length + 2) + hA.steps]
        (some (embed₁ A B (A.init x))) = some (embed₂ A B (B.halt z)) := by
    rw [Function.iterate_add_apply,
      iterate_lift (TM2.step A.program) (TM2.step (program A B)) (embed₁ A B)
        (step₁ A B) _ _ _ hA.evals_in_steps,
      Function.iterate_add_apply, transfer,
      iterate_lift (TM2.step B.program) (TM2.step (program A B)) (embed₂ A B)
        (step₂ A B) _ _ _ hB.evals_in_steps]
  refine ⟨⟨hB.steps + (2 * y.length + 2) + hA.steps, ?_⟩, ?_⟩
  · exact embed₁_init A B x ▸ embed₂_halt A B z ▸ hRun
  · exact Nat.add_le_add (Nat.add_le_add_right hB.steps_le_m _) hA.steps_le_m

/-- A polynomial with natural coefficients is monotone on natural inputs. -/
theorem polynomial_eval_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      intro a b hab
      simpa only [Polynomial.eval_add] using Nat.add_le_add (hp hab) (hq hab)
  | monomial n c =>
      intro a b hab
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

/-- Output-length bound derived from input length and the first program's pushes/time. -/
noncomputable def intermediateLengthPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (programPushes A.program) * p

/-- Polynomial obtained from both real time budgets and the actual transfer cost. -/
noncomputable def timePolynomial (p q : Polynomial ℕ) : Polynomial ℕ :=
  q.comp (intermediateLengthPolynomial A p) +
    Polynomial.C 2 * intermediateLengthPolynomial A p + Polynomial.C 2 + p

-- No composition-time conclusion is assumed: the actual constructed machine is used.
/-- The actual constructed finite machine inherits polynomial time from its two actual runs. -/
def executes_polynomial (f g : List Bool → List Bool) (p q : Polynomial ℕ)
    (hA : ∀ x, EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt (f x))) (p.eval x.length))
    (hB : ∀ y, EvalsToInTime (TM2.step B.program) (B.init y) (some (B.halt (g y))) (q.eval y.length))
    (x : List Bool) :
    EvalsToInTime (TM2.step (machine A B).program)
      ((machine A B).init x) (some ((machine A B).halt (g (f x))))
      ((timePolynomial A p q).eval x.length) := by
  have hL : (f x).length ≤ (intermediateLengthPolynomial A p).eval x.length := by
    simpa [intermediateLengthPolynomial, Nat.mul_comm] using Machine.output_length_le A x (f x) _ (hA x)
  have hq := polynomial_eval_monotone q hL
  have h := executes A B x (f x) (g (f x)) _ _ (hA x) (hB (f x))
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hq (Nat.mul_le_mul_left 2 hL)) 2) _

end Composition

end QEC.Coding.BitTuring
