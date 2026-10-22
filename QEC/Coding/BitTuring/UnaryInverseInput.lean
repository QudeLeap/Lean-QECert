import QEC.Coding.BitTuring.UnaryProductTrial

/-!
# Actual inverse-search initialization and unary delimiter writer

Three finite Boolean tapes parse the fixed factor, copy the modulus, drain the factor and
write literal one-target/zero-candidate delimiters. A separate actual unary delimiter writer
lets input retention carry a computed factor and its original modulus. Every phase, complete
clean run and exact count is proved. Neither initializer chooses a result.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.InverseInput
open Turing StateTransition
/-- Finite Boolean instruction type for this concrete parser and writer. -/
abbrev Statement := TM2.Stmt (fun _:Fin 3 => Bool) (Fin 3) (Option Bool)
/-- Concrete finite Boolean instructions, with all varying numbers only on tapes. -/
def program : Fin 3 → Statement
  | 0 => .pop 0 (fun _ h => h) (.branch (fun v => v.getD false)
      (.push 1 (fun _ => true) (.goto fun _ => 0)) (.goto fun _ => 1))
  | 1 => .pop 0 (fun _ h => h) (.branch (fun v => v.isSome)
      (.push 2 (fun _ => true) (.goto fun _ => 1))
      (.push 2 (fun _ => false) (.goto fun _ => 2)))
  | _ => .pop 1 (fun _ h => h) (.branch (fun v => v.isSome)
      (.push 2 (fun _ => true) (.goto fun _ => 2))
      (.push 2 (fun _ => false) (.push 2 (fun _ => false)
        (.push 2 (fun _ => true) (.load (fun _ => none) .halt)))))
/-- Actual fixed finite machine for this fully proved instruction closure. -/
def machine : Machine where
  K:=Fin 3
  input:=0
  output:=2
  Λ:=Fin 3
  main:=0
  σ:=Option Bool
  initial:=none
  program:=program
/-- Complete actual configuration with every tape and finite variable. -/
def cfg (l:Fin 3) (s b d:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 3 => Bool) (Fin 3) (Option Bool) := ⟨some l,v,![s,b,d]⟩
/-- Complete clean halt with only the output tape populated. -/
def halt (d:List Bool) : TM2.Cfg (fun _:Fin 3 => Bool) (Fin 3) (Option Bool) :=
  ⟨none,none,![[],[],d]⟩
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem parse_cons (s b d:List Bool) (v:Option Bool) :
    TM2.step program (cfg 0 (true::s) b d v)=some (cfg 0 s (true::b) d (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem parse_sep (s b d:List Bool) (v:Option Bool) :
    TM2.step program (cfg 0 (false::s) b d v)=some (cfg 1 s b d (some false)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem copy_cons (s b d:List Bool) (v:Option Bool) :
    TM2.step program (cfg 1 (true::s) b d v)=some (cfg 1 s b (true::d) (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem copy_nil (b d:List Bool) (v:Option Bool) :
    TM2.step program (cfg 1 [] b d v)=some (cfg 2 [] b (false::d) none) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem drain_cons (b d:List Bool) (v:Option Bool) :
    TM2.step program (cfg 2 [] (true::b) d v)=some (cfg 2 [] b (true::d) (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem drain_nil (d:List Bool) (v:Option Bool) :
    TM2.step program (cfg 2 [] [] d v)=some (halt (true::false::false::d)) := by
  simp [TM2.step,program,cfg,halt,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem run_parse (u:ℕ) (s b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step program))^[u+1]
      (some (cfg 0 (unary u++false::s) b d v))=some (cfg 1 s (unary u++b) d (some false)) := by
  induction u generalizing b d v with
  | zero => simp [unary,parse_sep]
  | succ u ih =>
    simp only [unary_succ,List.cons_append]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,parse_cons]
    rw [ih];simp [unary_append_cons]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem run_copy (q:ℕ) (b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step program))^[q+1]
      (some (cfg 1 (unary q) b d v))=some (cfg 2 [] b (false::(unary q++d)) none) := by
  induction q generalizing d v with
  | zero => simp [unary,copy_nil]
  | succ q ih =>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,copy_cons]
    rw [ih];simp [unary_append_cons]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem run_drain (u:ℕ) (d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step program))^[u+1]
      (some (cfg 2 [] (unary u) d v))=some (halt (true::false::false::(unary u++d))) := by
  induction u generalizing d v with
  | zero => simp [unary,drain_nil]
  | succ u ih =>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,drain_cons]
    rw [ih];simp [unary_append_cons]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem init_eq (u q:ℕ) : machine.init (pairInput u q)=cfg 0 (pairInput u q) [] [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem halt_eq (y:List Bool) : machine.halt y=halt y := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Complete counted actual instruction execution with a clean halt. -/
def exec (u q:ℕ) :
    EvalsToInTime (TM2.step machine.program) (machine.init (pairInput u q))
      (some (machine.halt (ProductAdvance.record 1 0 u q))) (2*u+q+3) := by
  refine ⟨⟨2*u+q+3,?_⟩,le_refl _⟩
  rw [init_eq,halt_eq]
  change (fun c => c.bind (TM2.step program))^[2*u+q+3]
    (some (cfg 0 (unary u++false::unary q) [] [] none))=
    some (halt (true::false::false::(unary u++false::unary q)))
  rw [show 2*u+q+3=(u+1)+(q+1)+(u+1) by omega]
  rw [Function.iterate_add_apply,run_parse,Function.iterate_add_apply,run_copy]
  simp only [List.append_nil]
  exact run_drain u (false::unary q) none
end QEC.Coding.BitTuring.UnaryArithmetic.InverseInput

namespace QEC.Coding.BitTuring.UnaryArithmetic.UnaryDelimiter
open Turing StateTransition
/-- Finite Boolean instruction type for this concrete parser and writer. -/
abbrev Statement := TM2.Stmt (fun _:Fin 2 => Bool) Bool (Option Bool)
/-- Concrete finite Boolean instructions, with all varying numbers only on tapes. -/
def program : Bool → Statement
  | true => .push 1 (fun _ => false) (.goto fun _ => false)
  | false => .pop 0 (fun _ h => h) (.branch (fun v => v.isSome)
      (.push 1 (fun _ => true) (.goto fun _ => false)) (.load (fun _ => none) .halt))
/-- Actual fixed finite machine for this fully proved instruction closure. -/
def machine : Machine where
  K:=Fin 2
  input:=0
  output:=1
  Λ:=Bool
  main:=true
  σ:=Option Bool
  initial:=none
  program:=program
/-- Complete actual configuration with every tape and finite variable. -/
def cfg (l:Bool) (s d:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 2 => Bool) Bool (Option Bool) := ⟨some l,v,![s,d]⟩
/-- Complete clean halt with only the output tape populated. -/
def halt (y:List Bool) : TM2.Cfg (fun _:Fin 2 => Bool) Bool (Option Bool) := ⟨none,none,![[],y]⟩
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem header (s:List Bool) : TM2.step program (cfg true s [] none)=some (cfg false s [false] none) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem copy_cons (s d:List Bool) (v:Option Bool) :
    TM2.step program (cfg false (true::s) d v)=some (cfg false s (true::d) (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem copy_nil (d:List Bool) (v:Option Bool) : TM2.step program (cfg false [] d v)=some (halt d) := by
  simp [TM2.step,program,cfg,halt,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem run_copy (n:ℕ) (d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1] (some (cfg false (unary n) d v))=
      some (halt (unary n++d)) := by
  induction n generalizing d v with
  | zero => simp [unary,copy_nil]
  | succ n ih =>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,copy_cons]
    rw [ih];simp [unary_append_cons]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem init_eq (n:ℕ) : machine.init (unary n)=cfg true (unary n) [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
theorem halt_eq (y:List Bool) : machine.halt y=halt y := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Complete counted actual instruction execution with a clean halt. -/
def exec (n:ℕ) : EvalsToInTime (TM2.step machine.program) (machine.init (unary n))
    (some (machine.halt (unary n++[false]))) (n+2) := by
  refine ⟨⟨n+2,?_⟩,le_refl _⟩
  rw [init_eq,halt_eq]
  change (fun c => c.bind (TM2.step program))^[n+2] (some (cfg true (unary n) [] none))=some (halt (unary n++[false]))
  rw [show n+2=(n+1)+1 by omega,Function.iterate_add_apply]
  simp only [Function.iterate_one,Option.bind_some,header]
  exact run_copy n [false] none
end QEC.Coding.BitTuring.UnaryArithmetic.UnaryDelimiter
