import QEC.Coding.BitTuring.UnarySquareRootTrial
import QEC.Coding.BitTuring.RetainedInput

/-!
# Actual candidate-only product trial update

Finite Boolean instructions preserve target, fixed factor and modulus. Failure advances only
the candidate; success returns it and drains every auxiliary tape. Counted phases and complete
clean runs derive linear update time. The unchanged parse/copy/drain labels reuse the
existing SquareRootAdvance program; only the candidate delimiter instruction is replaced. Actual retained modular trial composition derives the
quadratic body budget. No arithmetic, answer or time callback inhabits machine control.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.ProductAdvance
open Turing StateTransition
/-- Finite Boolean flag and optional tape head, with no natural registers. -/
abbrev Var := Bool × Option Bool
/-- Concrete finite Boolean instruction type for this actual parser/writer. -/
abbrev Statement := TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 6) Var

/-- Exact initial finite-variable state restored at every complete halt. -/
def reset : Var := (false, none)
/-- Real finite Boolean parse/copy/update/branch instructions, not semantic computation. -/
def program : Fin 6 → Statement
  | 2 => .pop 0 (fun v h => (v.1,h))
      (.branch (fun v => v.2.getD false)
        (.branch Prod.fst (.push 2 (fun _ => true) (.goto fun _ => 2))
          (.push 1 (fun _ => true) (.goto fun _ => 2)))
        (.branch Prod.fst (.goto fun _ => 3)
          (.push 1 (fun _ => false) (.goto fun _ => 3))))
  | l => SquareRootAdvance.program l

/-- Actual fixed finite machine for this proved instruction/selector closure. -/
def machine : Machine where
  K := Fin 3
  input := 0
  output := 2
  Λ := Fin 6
  main := 0
  σ := Var
  initial := reset
  program := program

/-- Full actual configuration containing every tape and finite variable. -/
def cfg (l : Fin 6) (s b d : List Bool) (v : Var) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 6) Var := ⟨some l,v,![s,b,d]⟩
/-- Complete clean halt with only the actual output tape populated. -/
def halt (w : List Bool) : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 6) Var :=
  ⟨none,reset,![[],[],w]⟩

/-- Consume the actually computed flag from the retained input record. -/
theorem read_flag (flag : Bool) (s : List Bool) :
    TM2.step program (cfg 0 (flag::s) [] [] reset) =
      some (cfg 1 s [] [] (flag,none)) := by
  simp [TM2.step,program,SquareRootAdvance.program,cfg,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- One concrete target cons transition with exact tape and variable updates. -/
theorem target_cons (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 1 (true::s) b d (flag,v)) =
      some (cfg 1 s (if flag then b else true::b) (d) (flag,some true)) := by
  cases flag <;> simp [TM2.step,program,SquareRootAdvance.program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])

/-- One concrete target sep transition with exact tape and variable updates. -/
theorem target_sep (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 1 (false::s) b d (flag,v)) =
      some (cfg 2 s (if flag then b else true::false::b) d (flag,some false)) := by
  cases flag <;> simp [TM2.step,program,SquareRootAdvance.program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])

/-- One concrete operand cons transition with exact tape and variable updates. -/
theorem operand_cons (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 2 (true::s) b d (flag,v)) =
      some (cfg 2 s (if flag then b else true::b) (if flag then true::d else d) (flag,some true)) := by
  cases flag <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])

/-- One concrete operand sep transition with exact tape and variable updates. -/
theorem operand_sep (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 2 (false::s) b d (flag,v)) =
      some (cfg 3 s (if flag then b else false::b) d (flag,some false)) := by
  cases flag <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])

/-- One concrete fixed-factor cons transition with exact tape and variable updates. -/
theorem factor_cons (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 3 (true::s) b d (flag,v)) =
      some (cfg 3 s (if flag then b else true::b) (d) (flag,some true)) := by
  cases flag <;> simp [TM2.step,program,SquareRootAdvance.program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])

/-- One concrete fixed-factor sep transition with exact tape and variable updates. -/
theorem factor_sep (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 3 (false::s) b d (flag,v)) =
      some (cfg 4 s (if flag then b else false::b) d (flag,some false)) := by
  cases flag <;> simp [TM2.step,program,SquareRootAdvance.program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])

/-- One concrete modulus cons transition with exact tape and variable updates. -/
theorem modulus_cons (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 4 (true::s) b d (flag,v)) =
      some (cfg 4 s (if flag then b else true::b) d (flag,some true)) := by
  cases flag <;> simp [TM2.step,program,SquareRootAdvance.program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])

/-- One concrete modulus nil true transition with exact tape and variable updates. -/
theorem modulus_nil_true (d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 4 [] [] d (true,v)) = some (halt (true::d)) := by
  simp [TM2.step,program,SquareRootAdvance.program,SquareRootAdvance.reset,cfg,halt,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- One concrete modulus nil false transition with exact tape and variable updates. -/
theorem modulus_nil_false (b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 4 [] b d (false,v)) = some (cfg 5 [] b d (false,none)) := by
  simp [TM2.step,program,SquareRootAdvance.program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]

/-- One concrete reverse cons transition with exact tape and variable updates. -/
theorem reverse_cons (x : Bool) (b d : List Bool) (v : Var) :
    TM2.step program (cfg 5 [] (x::b) d v) = some (cfg 5 [] b (x::d) (v.1,some x)) := by
  simp [TM2.step,program,SquareRootAdvance.program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- One concrete reverse nil transition with exact tape and variable updates. -/
theorem reverse_nil (d : List Bool) (v : Var) :
    TM2.step program (cfg 5 [] [] d v) = some (halt (false::d)) := by
  simp [TM2.step,program,SquareRootAdvance.program,SquareRootAdvance.reset,cfg,halt,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Counted complete run target false instruction phase, preserving the stated tapes. -/
theorem run_target_false (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 1 (unary n++false::x) b d (false,v))) =
      some (cfg 2 x (true::false::(unary n++b)) (d) (false,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,target_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,target_cons]
      rw [ih]
      simp [unary_append_cons]

/-- Counted complete run target true instruction phase, preserving the stated tapes. -/
theorem run_target_true (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 1 (unary n++false::x) b d (true,v))) =
      some (cfg 2 x (b) (d) (true,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,target_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,target_cons]
      rw [ih]
      simp

/-- Counted complete run operand false instruction phase, preserving the stated tapes. -/
theorem run_operand_false (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 2 (unary n++false::x) b d (false,v))) =
      some (cfg 3 x (false::(unary n++b)) (d) (false,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,operand_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,operand_cons]
      rw [ih]
      simp [unary_append_cons]

/-- Counted complete run operand true instruction phase, preserving the stated tapes. -/
theorem run_operand_true (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 2 (unary n++false::x) b d (true,v))) =
      some (cfg 3 x (b) (unary n++d) (true,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,operand_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,operand_cons]
      rw [ih]
      simp [unary_append_cons]

/-- Counted complete run fixed-factor false instruction phase, preserving the stated tapes. -/
theorem run_factor_false (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 3 (unary n++false::x) b d (false,v))) =
      some (cfg 4 x (false::(unary n++b)) (d) (false,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,factor_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,factor_cons]
      rw [ih]
      simp [unary_append_cons]

/-- Counted complete run fixed-factor true instruction phase, preserving the stated tapes. -/
theorem run_factor_true (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 3 (unary n++false::x) b d (true,v))) =
      some (cfg 4 x (b) (d) (true,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,factor_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,factor_cons]
      rw [ih]
      simp

/-- Counted complete run modulus false instruction phase, preserving the stated tapes. -/
theorem run_modulus_false (q : ℕ) (b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[q+1]
      (some (cfg 4 (unary q) b d (false,v))) =
      some (cfg 5 [] (unary q++b) d (false,none)) := by
  induction q generalizing b v with
  | zero => simp [unary,modulus_nil_false]
  | succ q ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,modulus_cons]
      rw [ih]
      simp [unary_append_cons]

/-- Counted complete run modulus true instruction phase, preserving the stated tapes. -/
theorem run_modulus_true (q : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[q+1]
      (some (cfg 4 (unary q) [] d (true,v))) = some (halt (true::d)) := by
  induction q generalizing v with
  | zero => simp [unary,modulus_nil_true]
  | succ q ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,modulus_cons]
      simpa using ih (some true)

/-- Counted complete run reverse instruction phase, preserving the stated tapes. -/
theorem run_reverse (b d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[b.length+1]
      (some (cfg 5 [] b d v)) = some (halt (false::(b.reverse++d))) := by
  induction b generalizing d v with
  | nil => simp [reverse_nil]
  | cons x b ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,reverse_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]


/-- Faithful product-trial tape record with one fixed operand and dynamic target/modulus. -/
def record (r a b q : ℕ) : List Bool := ModularTrial.input a b r q

/-- Reversed tape record actually built by the failure branch. -/
def falseBuffer (r a b q : ℕ) : List Bool :=
  unary q++false::(unary b++false::(unary a++true::false::unary r))

/-- Actual failure buffer reverses to the incremented faithful record. -/
theorem falseBuffer_eq (r a b q : ℕ) : falseBuffer r a b q=(record r (a+1) b q).reverse := by
  simp [falseBuffer,record,ModularTrial.input,UnaryOutputEquality.prefixInput,
    FactorTest.tripleInput,pairInput,unary,List.replicate_succ,List.append_assoc]

/-- Counted complete run true instruction phase, preserving the stated tapes. -/
theorem run_true (r a b q : ℕ) :
    (fun c => c.bind (TM2.step program))^[r+a+b+q+5]
      (some (cfg 0 (true::record r a b q) [] [] reset)) = some (halt (true::unary a)) := by
  rw [show r+a+b+q+5=(q+1)+(b+1)+(a+1)+(r+1)+1 by omega]
  rw [Function.iterate_add_apply]
  simp only [Function.iterate_one,Option.bind_some,read_flag]
  change (fun c => c.bind (TM2.step program))^[(q+1)+(b+1)+(a+1)+(r+1)]
    (some (cfg 1 (unary r++false::(unary a++false::(unary b++false::unary q))) [] []
      (true,none))) = _
  rw [Function.iterate_add_apply,run_target_true,Function.iterate_add_apply,run_operand_true,
    Function.iterate_add_apply,run_factor_true,run_modulus_true]
  simp

/-- Counted complete run false instruction phase, preserving the stated tapes. -/
theorem run_false (r a b q : ℕ) :
    (fun c => c.bind (TM2.step program))^[2*r+2*a+2*b+2*q+10]
      (some (cfg 0 (false::record r a b q) [] [] reset)) =
      some (halt (false::record r (a+1) b q)) := by
  have hlen : (record r (a+1) b q).length=r+a+b+q+4 := by
    simp [record,ModularTrial.input,UnaryOutputEquality.prefixInput_length,
      FactorTest.tripleInput_length];omega
  rw [show 2*r+2*a+2*b+2*q+10=
    ((record r (a+1) b q).length+1)+(q+1)+(b+1)+(a+1)+(r+1)+1 by omega]
  rw [Function.iterate_add_apply]
  simp only [Function.iterate_one,Option.bind_some,read_flag]
  change (fun c => c.bind (TM2.step program))^[
    ((record r (a+1) b q).length+1)+(q+1)+(b+1)+(a+1)+(r+1)]
    (some (cfg 1 (unary r++false::(unary a++false::(unary b++false::unary q))) [] []
      (false,none))) = _
  rw [Function.iterate_add_apply,run_target_false,Function.iterate_add_apply,run_operand_false,
    Function.iterate_add_apply,run_factor_false,Function.iterate_add_apply,run_modulus_false]
  simp only [List.append_nil]
  change (fun c => c.bind (TM2.step program))^[(record r (a+1) b q).length+1]
    (some (cfg 5 [] (falseBuffer r a b q) [] (false,none))) = _
  have hr := run_reverse (falseBuffer r a b q) [] (false,none)
  simpa only [falseBuffer_eq,List.length_reverse,List.reverse_reverse,List.append_nil] using hr


/-- Exact actual encoded record length controls every loop iteration. -/
theorem record_length (r a b q : ℕ) : (record r a b q).length=r+a+b+q+3 := by
  simp [record,ModularTrial.input,UnaryOutputEquality.prefixInput_length,
    FactorTest.tripleInput_length];omega

/-- Standard initialization is exactly the concrete complete parser/writer entry. -/
theorem init_eq (flag : Bool) (r a b q : ℕ) : machine.init (flag::record r a b q)=
    cfg 0 (flag::record r a b q) [] [] reset := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Standard halt is exactly the concrete complete clean output configuration. -/
theorem halt_eq (y : List Bool) : machine.halt y=halt y := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Mathematical output specification for both actual updater branches. -/
def output (flag : Bool) (r a b q : ℕ) : List Bool :=
  if flag then true::unary a else false::record r (a+1) b q

/-- Complete counted steps of both actual update branches. -/
def steps (flag : Bool) (r a b q : ℕ) : ℕ :=
  if flag then r+a+b+q+5 else 2*r+2*a+2*b+2*q+10

/-- Complete actual clean instruction run has its counted or derived time bound. -/
def exec (flag : Bool) (r a b q : ℕ) :
    EvalsToInTime (TM2.step machine.program) (machine.init (flag::record r a b q))
      (some (machine.halt (output flag r a b q))) (2*(flag::record r a b q).length+3) := by
  refine ⟨⟨steps flag r a b q,?_⟩,?_⟩
  · rw [init_eq,halt_eq]
    cases flag
    · exact run_false r a b q
    · exact run_true r a b q
  · rw [List.length_cons,record_length]
    cases flag <;> simp [steps] <;> omega

end QEC.Coding.BitTuring.UnaryArithmetic.ProductAdvance

namespace QEC.Coding.BitTuring.UnaryArithmetic.ProductTrial
open Turing StateTransition

/-- Actual fixed finite machine for this proved instruction/selector closure. -/
def machine : Machine :=
  Composition.machine (RetainedInput.machine ModularTrial.machine) ProductAdvance.machine

/-- Mathematical polynomial derived from the whole actual instruction execution. -/
noncomputable def time : Polynomial ℕ :=
  ModularTrial.time+Polynomial.C 7*Polynomial.X+Polynomial.C 17

/-- Mathematical specification of the independently executed product-trial body output. -/
def result (r a b q : ℕ) : List Bool :=
  ProductAdvance.output (decide ((a*b)%q=r)) r a b q

/-- Complete genuine instruction execution satisfies its derived input polynomial. -/
noncomputable def polyExec (r a b q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (ProductAdvance.record r a b q))
      (some (machine.halt (result r a b q)))
      (time.eval (ProductAdvance.record r a b q).length) := by
  let L := (ProductAdvance.record r a b q).length
  let flag := decide ((a*b)%q=r)
  have hA : EvalsToInTime (TM2.step (RetainedInput.machine ModularTrial.machine).program)
      ((RetainedInput.machine ModularTrial.machine).init (ProductAdvance.record r a b q))
      (some ((RetainedInput.machine ModularTrial.machine).halt
        (flag::ProductAdvance.record r a b q))) (ModularTrial.time.eval L+3*L+8) := by
    simpa [ProductAdvance.record,L,Nat.add_assoc] using
      RetainedInput.executes ModularTrial.machine (ModularTrial.input a b r q) [flag] _
        (ModularTrial.polyExec a b r q hq)
  have hB : EvalsToInTime (TM2.step ProductAdvance.machine.program)
      (ProductAdvance.machine.init (flag::ProductAdvance.record r a b q))
      (some (ProductAdvance.machine.halt (result r a b q))) (2*L+5) := by
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,result] using
      ProductAdvance.exec flag r a b q
  have h := Composition.executes (RetainedInput.machine ModularTrial.machine) ProductAdvance.machine
    _ _ _ _ _ hA hB
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  change (2*L+5)+(2*(flag::ProductAdvance.record r a b q).length+2)+
    (ModularTrial.time.eval L+3*L+8)≤time.eval L
  simp only [List.length_cons,time,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  dsimp only [L]
  omega

/-- The actual composed body has disjoint input and output channels. -/
theorem input_ne_output : machine.input≠machine.output := by
  simp [machine,Composition.machine]

end QEC.Coding.BitTuring.UnaryArithmetic.ProductTrial
