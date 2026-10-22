import QEC.Coding.BitTuring.Composition

/-!
# Actual unary multiplication by a finite-control Boolean Turing machine

All unbounded natural data is represented by Boolean stack lengths. Five stacks, six labels
and one finite Option-Bool variable suffice to parse a faithful delimiter encoding, consume
one first-operand bit per pass, duplicate and restore the second operand, and clean up.

The exact counted execution is `(a+1)*(2*b+4)` TM2 label steps. The standard Mathlib
polynomial-time certificate derives from that actual execution and the bound `2*(L+1)^2`,
where L is the actual unary encoded-input bit length. This is not a claim of polynomial time
in binary natural-number input length, nor a complete PK22 runtime bound. The mathematical
time polynomial does not participate in machine execution.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic

open Turing StateTransition

/-- Actual six-label Boolean instructions: parse operands, duplicate/restore the second, drain and halt. -/
def multiplicationProgram : Fin 6 → TM2.Stmt (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool)
  | 0 => .pop 0 (fun _ h => h)
      (.branch (fun v => v.getD false)
        (.push 1 (fun _ => true) (.goto fun _ => 0)) (.goto fun _ => 1))
  | 1 => .pop 0 (fun _ h => h)
      (.branch Option.isSome
        (.push 2 (fun v => v.getD false) (.goto fun _ => 1)) (.goto fun _ => 2))
  | 2 => .pop 1 (fun _ h => h)
      (.branch Option.isSome (.goto fun _ => 3) (.goto fun _ => 5))
  | 3 => .pop 2 (fun _ h => h)
      (.branch Option.isSome
        (.push 3 (fun v => v.getD false) (.push 4 (fun v => v.getD false) (.goto fun _ => 3)))
        (.goto fun _ => 4))
  | 4 => .pop 3 (fun _ h => h)
      (.branch Option.isSome
        (.push 2 (fun v => v.getD false) (.goto fun _ => 4)) (.goto fun _ => 2))
  | _ => .pop 2 (fun _ h => h)
      (.branch Option.isSome (.goto fun _ => 5) .halt)

/-- Fixed finite controls and Boolean stacks; variable natural data never inhabits machine variables. -/
def multiplicationMachine : Machine where
  K := Fin 5
  input := 0
  output := 4
  Λ := Fin 6
  main := 0
  σ := Option Bool
  initial := none
  program := multiplicationProgram

/-- Complete five-stack configuration: input, first operand, second operand, buffer and output. -/
def multiplicationCfg (phase : Fin 6) (source a b buffer output : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  ⟨some phase,v,![source,a,b,buffer,output]⟩

/-- Exact halt with reset variables and every non-output stack empty. -/
def multiplicationHalt (output : List Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  ⟨none,none,![[],[],[],[],output]⟩

/-- Faithful unary bit-string encoding of a natural number. -/
def unary (n : ℕ) := List.replicate n true

/-- Pair encoding with a single false delimiter separating two all-true unary strings. -/
def pairInput (a b : ℕ) := unary a ++ false :: unary b

/-- Consume one true first-operand bit into its stack. -/
theorem parseA_true (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 0 (true :: s) a b buf d v) = some (multiplicationCfg 0 s (true :: a) b buf d (some true)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Consume the delimiter and switch to second-operand parsing. -/
theorem parseA_separator (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 0 (false :: s) a b buf d v) = some (multiplicationCfg 1 s a b buf d (some false)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Consume one second-operand bit into its stack. -/
theorem parseB_cons (x : Bool) (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 1 (x :: s) a b buf d v) = some (multiplicationCfg 1 s a (x :: b) buf d (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Finish parsing in one actual step with reset variables. -/
theorem parseB_nil (a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 1 [] a b buf d v) = some (multiplicationCfg 2 [] a b buf d none) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]

/-- Consume one first-operand bit and enter the duplication pass. -/
theorem outer_cons (x : Bool) (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 2 s (x :: a) b buf d v) = some (multiplicationCfg 3 s a b buf d (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- An empty first operand enters the final cleanup. -/
theorem outer_nil (s b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 2 s [] b buf d v) = some (multiplicationCfg 5 s [] b buf d none) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]

/-- Move one second-operand bit to the buffer and duplicate it into output. -/
theorem copyB_cons (x : Bool) (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 3 s a (x :: b) buf d v) = some (multiplicationCfg 3 s a b (x :: buf) (x :: d) (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- An empty second-operand stack enters restoration. -/
theorem copyB_nil (s a buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 3 s a [] buf d v) = some (multiplicationCfg 4 s a [] buf d none) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]

/-- Restore one buffered bit into the second-operand stack. -/
theorem restore_cons (x : Bool) (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 4 s a b (x :: buf) d v) = some (multiplicationCfg 4 s a (x :: b) buf d (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- A drained buffer returns to the outer loop with reset variables. -/
theorem restore_nil (s a b d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 4 s a b [] d v) = some (multiplicationCfg 2 s a b [] d none) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]

/-- Drain one retained second-operand bit during final cleanup. -/
theorem clean_cons (x : Bool) (b d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 5 [] [] (x :: b) [] d v) = some (multiplicationCfg 5 [] [] b [] d (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- A drained machine reaches its exact complete halt. -/
theorem clean_nil (d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 5 [] [] [] [] d v) = some (multiplicationHalt d) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, multiplicationHalt, TM2.stepAux, TM2.Cfg.mk.injEq]

/-- Zero has the empty unary bit string. -/
@[simp] theorem unary_zero : unary 0 = [] := rfl

/-- Successor adds one true bit. -/
@[simp] theorem unary_succ (n : ℕ) : unary (n + 1) = true :: unary n := by
  simp [unary, List.replicate_succ]

/-- A true bit after a unary prefix extends that prefix. -/
theorem unary_append_cons (n : ℕ) (d : List Bool) :
    unary n ++ true :: d = unary (n + 1) ++ d := by
  simp [unary, List.replicate_add, List.append_assoc]

/-- Concatenating two unary strings represents their sum. -/
theorem unary_add (a b : ℕ) : unary (a + b) = unary a ++ unary b :=
  List.replicate_add a b true

/-- The actual unary bit-string length is the encoded natural value. -/
theorem unary_length (n : ℕ) : (unary n).length = n := by simp [unary]

/-- Unary output encoding never identifies different natural values. -/
theorem unary_injective : Function.Injective unary := by
  intro a b h
  simpa only [unary_length] using congrArg List.length h

/-- The true prefix decodes exactly the first unary operand. -/
theorem takeWhile_pairInput (a b : ℕ) : (pairInput a b).takeWhile id = unary a := by
  induction a with
  | zero => simp [pairInput]
  | succ a ih => simpa [pairInput, unary_succ] using congrArg (List.cons true) ih

/-- Removing the true prefix exposes exactly the delimiter and second operand. -/
theorem dropWhile_pairInput (a b : ℕ) : (pairInput a b).dropWhile id = false :: unary b := by
  induction a with
  | zero => simp [pairInput]
  | succ a ih => simpa [pairInput, unary_succ] using ih

/-- The delimiter input encoding never identifies different natural pairs. -/
theorem pairInput_injective : Function.Injective (fun x : ℕ × ℕ => pairInput x.1 x.2) := by
  intro x y h
  have ha : unary x.1 = unary y.1 := by
    simpa only [takeWhile_pairInput] using congrArg (List.takeWhile id) h
  have hb : false :: unary x.2 = false :: unary y.2 := by
    simpa only [dropWhile_pairInput] using congrArg (List.dropWhile id) h
  exact Prod.ext (unary_injective ha) (unary_injective (List.cons.inj hb).2)

/-- Parsing includes all first-operand bits and the delimiter, with its actual step count. -/
theorem run_parseA (n : ℕ) (s a b buf d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 0 (unary n ++ false :: s) a b buf d v)) =
      some (multiplicationCfg 1 s (unary n ++ a) b buf d (some false)) := by
  induction n generalizing a v with
  | zero => simp [parseA_separator]
  | succ n ih =>
      simp only [unary_succ, List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, parseA_true]
      simpa only [unary_append_cons, unary_succ, List.cons_append] using ih (true :: a) (some true)

/-- Second-operand parsing includes its empty-stack test and exact control reset. -/
theorem run_parseB (n : ℕ) (a b buf d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 1 (unary n) a b buf d v)) =
      some (multiplicationCfg 2 [] a (unary n ++ b) buf d none) := by
  induction n generalizing b v with
  | zero => simp [parseB_nil]
  | succ n ih =>
      simp only [unary_succ, List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, parseB_cons]
      simpa only [unary_append_cons, unary_succ, List.cons_append] using ih (true :: b) (some true)

/-- Duplicate a unary second operand into output through the buffer in length plus one steps. -/
theorem run_copyB (n : ℕ) (s a buf d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 3 s a (unary n) buf d v)) =
      some (multiplicationCfg 4 s a [] (unary n ++ buf) (unary n ++ d) none) := by
  induction n generalizing buf d v with
  | zero => simp [copyB_nil]
  | succ n ih =>
      simp only [unary_succ, List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, copyB_cons]
      simpa only [unary_append_cons, unary_succ, List.cons_append] using ih (true :: buf) (true :: d) (some true)

/-- Restore the unary second operand and drain its buffer in length plus one steps. -/
theorem run_restoreB (n : ℕ) (s a b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 4 s a b (unary n) d v)) =
      some (multiplicationCfg 2 s a (unary n ++ b) [] d none) := by
  induction n generalizing b v with
  | zero => simp [restore_nil]
  | succ n ih =>
      simp only [unary_succ, List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, restore_cons]
      simpa only [unary_append_cons, unary_succ, List.cons_append] using ih (true :: b) (some true)

/-- Final cleanup drains all retained bits, resets variables, and halts. -/
theorem run_cleanB (n : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 5 [] [] (unary n) [] d v)) = some (multiplicationHalt d) := by
  induction n generalizing v with
  | zero => simp [clean_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, clean_cons]
      exact ih (some true)

/-- The actual outer loop produces the product string and includes final cleanup in its count. -/
theorem run_outer (a b : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[a * (2 * b + 3) + b + 2]
      (some (multiplicationCfg 2 [] (unary a) (unary b) [] d v)) =
      some (multiplicationHalt (unary (a * b) ++ d)) := by
  induction a generalizing d v with
  | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, unary_zero, List.nil_append]
      rw [show b + 2 = (b + 1) + 1 by omega, Function.iterate_succ_apply]
      simp only [Option.bind_some, outer_nil]
      exact run_cleanB b d none
  | succ a ih =>
      have ht : (a + 1) * (2 * b + 3) + b + 2 =
          ((a * (2 * b + 3) + b + 2) + (b + 1)) + (b + 1) + 1 := by ring
      rw [ht, Function.iterate_succ_apply]
      simp only [unary_succ, Option.bind_some, outer_cons]
      rw [Function.iterate_add_apply, run_copyB]
      simp only [List.append_nil]
      rw [Function.iterate_add_apply, run_restoreB]
      simp only [List.append_nil]
      simpa only [Nat.add_mul, Nat.one_mul, unary_add, List.append_assoc] using ih (unary b ++ d) none

/-- Actual whole-program execution computes the natural product, including both parsers and cleanup. -/
theorem run_multiplication (a b : ℕ) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[(a + 1) * (2 * b + 4)]
      (some (multiplicationCfg 0 (pairInput a b) [] [] [] [] none)) =
      some (multiplicationHalt (unary (a * b))) := by
  have ht : (a + 1) * (2 * b + 4) =
      ((a * (2 * b + 3) + b + 2) + (b + 1)) + (a + 1) := by ring
  rw [ht, Function.iterate_add_apply]
  simp only [pairInput]
  rw [run_parseA]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply, run_parseB]
  simp only [List.append_nil]
  rw [run_outer]
  simp

/-- The raw parser entry is exactly the standard Boolean machine input configuration. -/
theorem machine_init_eq (a b : ℕ) :
    multiplicationMachine.init (pairInput a b) =
      multiplicationCfg 0 (pairInput a b) [] [] [] [] none := by
  simp [Machine.init, multiplicationMachine, multiplicationCfg, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- The raw completed configuration is exactly the standard Boolean machine output. -/
theorem machine_halt_eq (d : List Bool) :
    multiplicationMachine.halt d = multiplicationHalt d := by
  simp [Machine.halt, multiplicationMachine, multiplicationHalt, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Real counted execution with budget `(a+1)*(2*b+4)`, constructed from whole-program iteration. -/
def multiplicationExec (a b : ℕ) :
    EvalsToInTime (TM2.step multiplicationMachine.program)
      (multiplicationMachine.init (pairInput a b))
      (some (multiplicationMachine.halt (unary (a * b)))) ((a + 1) * (2 * b + 4)) := by
  refine ⟨⟨(a + 1) * (2 * b + 4), ?_⟩, le_refl _⟩
  exact (machine_init_eq a b).symm ▸ (machine_halt_eq (unary (a * b))).symm ▸ run_multiplication a b

/-- Exact actual bit-string length of the faithful unary pair encoding. -/
theorem pairInput_length (a b : ℕ) : (pairInput a b).length = a + b + 1 := by
  simp [pairInput, unary]
  omega

/-- The derived actual execution budget is quadratic in unary encoded-input bit length. -/
theorem multiplication_steps_le (a b : ℕ) :
    (a + 1) * (2 * b + 4) ≤ 2 * ((pairInput a b).length + 1) ^ 2 := by
  have ha : a + 1 ≤ (pairInput a b).length + 1 := by rw [pairInput_length]; omega
  have hb : b + 2 ≤ (pairInput a b).length + 1 := by rw [pairInput_length]; omega
  calc
    (a + 1) * (2 * b + 4) = 2 * ((a + 1) * (b + 2)) := by ring
    _ ≤ 2 * (((pairInput a b).length + 1) * ((pairInput a b).length + 1)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul ha hb)
    _ = 2 * ((pairInput a b).length + 1) ^ 2 := by ring

/-- Mathematical quadratic time bound; it never runs inside the finite machine. -/
noncomputable def multiplicationTime : Polynomial ℕ := Polynomial.C 2 * (Polynomial.X + 1) ^ 2

/-- The actual constructed multiplication run satisfies the quadratic encoded-input bound. -/
noncomputable def multiplicationPolyExec (a b : ℕ) :
    EvalsToInTime (TM2.step multiplicationMachine.program)
      (multiplicationMachine.init (pairInput a b))
      (some (multiplicationMachine.halt (unary (a * b))))
      (multiplicationTime.eval (pairInput a b).length) := by
  have h := multiplicationExec a b
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simpa [multiplicationTime] using multiplication_steps_le a b

/-- Standard Mathlib polynomial-time certificate for this real machine and faithful unary encodings. -/
noncomputable def multiplicationComputableInPolyTime :
    TM2ComputableInPolyTime (fun x : ℕ × ℕ => pairInput x.1 x.2) unary (fun x => x.1 * x.2) where
  tm := multiplicationMachine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := multiplicationTime
  outputsFun := fun x => by
    change TM2OutputsInTime multiplicationMachine.toFinTM2
      (List.map id (pairInput x.1 x.2)) (some (List.map id (unary (x.1 * x.2))))
      (multiplicationTime.eval (pairInput x.1 x.2).length)
    have h := Machine.outputsInTime multiplicationMachine _ _ _ (multiplicationPolyExec x.1 x.2)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h


end QEC.Coding.BitTuring.UnaryArithmetic
