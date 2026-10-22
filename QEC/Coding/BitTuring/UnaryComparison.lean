import QEC.Coding.BitTuring.UnaryMultiplication

/-!
# Actual unary comparison by a finite-control Boolean Turing machine

Three Boolean stacks, four labels and Option-Bool variables parse a faithful natural pair,
consume paired operand bits, detect equality or strict order, drain leftover bits, and emit
`[decide (a ≤ b), decide (a = b)]`. Every complete run includes parsing, cleanup and reset.
The actual count is `if b<a then 2*a+2 else a+b+2`, at most `2*(L+1)` in unary input length L.

The standard polynomial-time certificate derives from actual finite instructions and counted
execution. Unary input length is not binary natural-number input length, and this arithmetic
prerequisite does not certify complete PK22 generation/runtime. Boolean is an encoding alphabet.
The mathematical bound and specification comparisons do not participate in machine execution.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

/-- Emit two fixed finite comparison bits and reset variables before actual halt. -/
def comparisonEmit (le eq : Bool) : TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .load (fun _ => none) (.push 2 (fun _ => eq) (.push 2 (fun _ => le) .halt))

/-- Parse the first operand, cancel paired bits, drain leftovers and emit the correct outcome. -/
def comparisonProgram : Fin 4 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool)
  | 0 => .pop 0 (fun _ h => h)
      (.branch (fun v => v.getD false)
        (.push 1 (fun _ => true) (.goto fun _ => 0)) (.goto fun _ => 1))
  | 1 => .pop 0 (fun _ h => h)
      (.branch Option.isSome
        (.pop 1 (fun _ h => h)
          (.branch Option.isSome (.goto fun _ => 1) (.goto fun _ => 3)))
        (.pop 1 (fun _ h => h)
          (.branch Option.isSome (.goto fun _ => 2) (comparisonEmit true true))))
  | 2 => .pop 1 (fun _ h => h)
      (.branch Option.isSome (.goto fun _ => 2) (comparisonEmit false false))
  | _ => .pop 0 (fun _ h => h)
      (.branch Option.isSome (.goto fun _ => 3) (comparisonEmit true false))

/-- Three Boolean stacks and finite labels/variables; no unbounded natural register. -/
def comparisonMachine : Machine where
  K := Fin 3
  input := 0
  output := 2
  Λ := Fin 4
  main := 0
  σ := Option Bool
  initial := none
  program := comparisonProgram

/-- Complete parser/matching configuration with source, first operand and output stacks. -/
def comparisonCfg (phase : Fin 4) (source a output : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  ⟨some phase,v,![source,a,output]⟩

/-- Exact halted output with both working stacks empty and variables reset. -/
def comparisonHalt (output : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  ⟨none,none,![[],[],output]⟩

/-- Move one first-operand bit from input into its working stack. -/
theorem comparison_parse_true (s a d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 0 (true :: s) a d v) =
      some (comparisonCfg 0 s (true :: a) d (some true)) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Consume the delimiter and enter matching. -/
theorem comparison_parse_separator (s a d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 0 (false :: s) a d v) =
      some (comparisonCfg 1 s a d (some false)) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Consume one bit from each operand in one actual label step. -/
theorem comparison_both_cons (x y : Bool) (s a d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 1 (x :: s) (y :: a) d v) =
      some (comparisonCfg 1 s a d (some y)) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Simultaneous exhaustion emits equality and non-strict comparison bits. -/
theorem comparison_both_nil (d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 1 [] [] d v) =
      some (comparisonHalt (true :: true :: d)) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, comparisonHalt, comparisonEmit,
    TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- A first-operand leftover selects the greater-than cleanup. -/
theorem comparison_gt (x : Bool) (a d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 1 [] (x :: a) d v) =
      some (comparisonCfg 2 [] a d (some x)) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- A second-operand leftover selects the less-than cleanup. -/
theorem comparison_lt (x : Bool) (s d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 1 (x :: s) [] d v) =
      some (comparisonCfg 3 s [] d none) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Drain one first-operand leftover bit. -/
theorem comparison_drainA_cons (x : Bool) (a d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 2 [] (x :: a) d v) =
      some (comparisonCfg 2 [] a d (some x)) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Complete greater-than cleanup, emit false/false and reset. -/
theorem comparison_drainA_nil (d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 2 [] [] d v) =
      some (comparisonHalt (false :: false :: d)) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, comparisonHalt, comparisonEmit,
    TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Drain one second-operand leftover bit. -/
theorem comparison_drainInput_cons (x : Bool) (s d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 3 (x :: s) [] d v) =
      some (comparisonCfg 3 s [] d (some x)) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Complete less-than cleanup, emit true/false and reset. -/
theorem comparison_drainInput_nil (d : List Bool) (v : Option Bool) :
    TM2.step comparisonProgram (comparisonCfg 3 [] [] d v) =
      some (comparisonHalt (true :: false :: d)) := by
  simp [TM2.step, comparisonProgram, comparisonCfg, comparisonHalt, comparisonEmit,
    TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Parse the faithful first operand and delimiter in exactly length plus one steps. -/
theorem comparison_run_parse (n : ℕ) (s a d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step comparisonProgram))^[n + 1]
      (some (comparisonCfg 0 (unary n ++ false :: s) a d v)) =
      some (comparisonCfg 1 s (unary n ++ a) d (some false)) := by
  induction n generalizing a v with
  | zero => simp [comparison_parse_separator]
  | succ n ih =>
      simp only [unary_succ, List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, comparison_parse_true]
      simpa only [unary_append_cons, unary_succ, List.cons_append] using ih (true :: a) (some true)

/-- Drain all first-operand leftover bits, including emission and reset. -/
theorem comparison_run_drainA (n : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step comparisonProgram))^[n + 1]
      (some (comparisonCfg 2 [] (unary n) d v)) =
      some (comparisonHalt (false :: false :: d)) := by
  induction n generalizing v with
  | zero => simp [comparison_drainA_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, comparison_drainA_cons]
      exact ih (some true)

/-- Drain all second-operand leftover bits, including emission and reset. -/
theorem comparison_run_drainInput (n : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step comparisonProgram))^[n + 1]
      (some (comparisonCfg 3 (unary n) [] d v)) =
      some (comparisonHalt (true :: false :: d)) := by
  induction n generalizing v with
  | zero => simp [comparison_drainInput_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, comparison_drainInput_cons]
      exact ih (some true)

/-- Paired equal-length cancellation reaches the exact equality output. -/
theorem comparison_run_equal (a : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step comparisonProgram))^[a + 1]
      (some (comparisonCfg 1 (unary a) (unary a) d v)) =
      some (comparisonHalt (true :: true :: d)) := by
  induction a generalizing v with
  | zero => simp [comparison_both_nil]
  | succ a ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, comparison_both_cons]
      exact ih (some true)

/-- Cancel the shared prefix and drain the longer second operand before less-than output. -/
theorem comparison_run_less (a r : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step comparisonProgram))^[a + r + 2]
      (some (comparisonCfg 1 (unary (a + r + 1)) (unary a) d v)) =
      some (comparisonHalt (true :: false :: d)) := by
  induction a generalizing v with
  | zero =>
      simp only [Nat.zero_add, unary_succ, unary_zero]
      rw [show r + 2 = (r + 1) + 1 by omega, Function.iterate_succ_apply]
      simp only [Option.bind_some, comparison_lt]
      exact comparison_run_drainInput r d none
  | succ a ih =>
      rw [show a + 1 + r + 1 = (a + r + 1) + 1 by omega]
      simp only [unary_succ]
      rw [show a + 1 + r + 2 = (a + r + 2) + 1 by omega, Function.iterate_succ_apply]
      simp only [Option.bind_some, comparison_both_cons]
      exact ih (some true)

/-- Cancel the shared prefix and drain the longer first operand before greater-than output. -/
theorem comparison_run_greater (b r : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step comparisonProgram))^[b + r + 2]
      (some (comparisonCfg 1 (unary b) (unary (b + r + 1)) d v)) =
      some (comparisonHalt (false :: false :: d)) := by
  induction b generalizing v with
  | zero =>
      simp only [Nat.zero_add, unary_succ, unary_zero]
      rw [show r + 2 = (r + 1) + 1 by omega, Function.iterate_succ_apply]
      simp only [Option.bind_some, comparison_gt]
      exact comparison_run_drainA r d (some true)
  | succ b ih =>
      rw [show b + 1 + r + 1 = (b + r + 1) + 1 by omega]
      simp only [unary_succ]
      rw [show b + 1 + r + 2 = (b + r + 2) + 1 by omega, Function.iterate_succ_apply]
      simp only [Option.bind_some, comparison_both_cons]
      exact ih (some true)

/-- Semantic output specification, never evaluated by the finite comparison program. -/
def comparisonBits (a b : ℕ) : List Bool := [decide (a ≤ b), decide (a = b)]
/-- Count derived from actual parser/matching/cleanup execution, not a machine cost field. -/
def comparisonSteps (a b : ℕ) := if b < a then 2 * a + 2 else a + b + 2

/-- Whole actual program execution computes both comparison bits with exact halt and count. -/
theorem run_comparison (a b : ℕ) :
    (fun c => c.bind (TM2.step comparisonProgram))^[comparisonSteps a b]
      (some (comparisonCfg 0 (pairInput a b) [] [] none)) =
      some (comparisonHalt (comparisonBits a b)) := by
  rcases lt_trichotomy a b with h | h | h
  · let r := b - a - 1
    have hb : b = a + r + 1 := by dsimp [r]; omega
    have hstep : comparisonSteps a b = (a + r + 2) + (a + 1) := by
      simp [comparisonSteps, not_lt.mpr (le_of_lt h)]
      omega
    rw [hstep, Function.iterate_add_apply]
    simp only [pairInput]
    rw [comparison_run_parse]
    simp only [List.append_nil]
    have hout : comparisonBits a b = [true,false] := by
      simp [comparisonBits, le_of_lt h, ne_of_lt h]
    rw [hout, hb, comparison_run_less]
  · subst b
    rw [show comparisonSteps a a = (a + 1) + (a + 1) by simp [comparisonSteps]; omega,
      Function.iterate_add_apply]
    simp only [pairInput]
    rw [comparison_run_parse]
    simp only [List.append_nil]
    rw [comparison_run_equal]
    simp [comparisonBits]
  · let r := a - b - 1
    have ha : a = b + r + 1 := by dsimp [r]; omega
    have hstep : comparisonSteps a b = (b + r + 2) + (a + 1) := by
      simp [comparisonSteps, h]
      omega
    rw [hstep, Function.iterate_add_apply]
    simp only [pairInput]
    rw [comparison_run_parse]
    simp only [List.append_nil]
    have hout : comparisonBits a b = [false,false] := by
      simp [comparisonBits, not_le.mpr h, ne_of_gt h]
    rw [hout, ha, comparison_run_greater]

/-- The raw parser entry equals the standard Boolean machine input configuration. -/
theorem comparison_init_eq (a b : ℕ) :
    comparisonMachine.init (pairInput a b) = comparisonCfg 0 (pairInput a b) [] [] none := by
  simp [Machine.init, comparisonMachine, comparisonCfg, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- The raw completed configuration equals the standard Boolean machine output. -/
theorem comparison_halt_eq (d : List Bool) : comparisonMachine.halt d = comparisonHalt d := by
  simp [Machine.halt, comparisonMachine, comparisonHalt, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Actual counted execution certificate assembled from the whole-program run. -/
def comparisonExec (a b : ℕ) :
    EvalsToInTime (TM2.step comparisonMachine.program)
      (comparisonMachine.init (pairInput a b))
      (some (comparisonMachine.halt (comparisonBits a b))) (comparisonSteps a b) := by
  refine ⟨⟨comparisonSteps a b, ?_⟩, le_refl _⟩
  exact (comparison_init_eq a b).symm ▸ (comparison_halt_eq (comparisonBits a b)).symm ▸
    run_comparison a b

/-- Actual count is linear in the faithful unary encoded-input bit length. -/
theorem comparison_steps_le (a b : ℕ) : comparisonSteps a b ≤ 2 * ((pairInput a b).length + 1) := by
  rw [pairInput_length]
  unfold comparisonSteps
  split_ifs <;> omega

/-- Mathematical linear time polynomial; never machine data or execution. -/
noncomputable def comparisonTime : Polynomial ℕ := Polynomial.C 2 * (Polynomial.X + 1)

/-- The real counted run satisfies the linear encoded-input polynomial bound. -/
noncomputable def comparisonPolyExec (a b : ℕ) :
    EvalsToInTime (TM2.step comparisonMachine.program)
      (comparisonMachine.init (pairInput a b))
      (some (comparisonMachine.halt (comparisonBits a b)))
      (comparisonTime.eval (pairInput a b).length) := by
  have h := comparisonExec a b
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simpa [comparisonTime] using comparison_steps_le a b

/-- Faithful two-bit encoding of a Boolean pair. -/
def boolPairBits (x : Bool × Bool) : List Bool := [x.1,x.2]

/-- The output encoding distinguishes all Boolean pairs. -/
theorem boolPairBits_injective : Function.Injective boolPairBits := by
  intro x y h
  have hx := List.cons.inj h
  exact Prod.ext hx.1 (List.cons.inj hx.2).1

/-- Standard Mathlib certificate derived from actual execution and faithful encodings. -/
noncomputable def comparisonComputableInPolyTime :
    TM2ComputableInPolyTime (fun x : ℕ × ℕ => pairInput x.1 x.2) boolPairBits
      (fun x => (decide (x.1 ≤ x.2), decide (x.1 = x.2))) where
  tm := comparisonMachine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := comparisonTime
  outputsFun := fun x => by
    change TM2OutputsInTime comparisonMachine.toFinTM2
      (List.map id (pairInput x.1 x.2)) (some (List.map id (comparisonBits x.1 x.2)))
      (comparisonTime.eval (pairInput x.1 x.2).length)
    have h := Machine.outputsInTime comparisonMachine _ _ _ (comparisonPolyExec x.1 x.2)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h

end QEC.Coding.BitTuring.UnaryArithmetic
