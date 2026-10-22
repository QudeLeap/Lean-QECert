import QEC.Coding.BitTuring.UnaryFieldProjection
import Mathlib.Data.ZMod.Basic

/-!
# Actual canonical unary modular negation

A finite Boolean flag remembers whether the first unary operand is zero. Actual parsing
stores both operands; real cancellation removes one modulus bit per stored operand bit.
The nonzero branch copies the remaining q-a bits, while the zero branch drains q and emits
canonical zero. Counted phases and clean complete runs derive linear unary-input time,
faithful canonical inputs and standard true-ZMod-negation certificates. No answer/cost
callback or varying natural register executes.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation
open Turing StateTransition
/-- Finite optional-bit and nonzero flag; no varying natural register. -/
abbrev Var := Option Bool×Bool
/-- Finite Boolean instruction type. -/
abbrev Statement := TM2.Stmt (fun _:Fin 4=>Bool) (Fin 5) Var
/-- Reset finite variable state, including the zero/nonzero flag. -/
def reset : Var := (none,false)
/-- Actual finite Boolean instructions with varying naturals only on tapes. -/
def program : Fin 5→Statement
  | 0=>.pop 0 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.getD false)
      (.push 1 (fun _=>true) (.load (fun v=>(v.1,true)) (.goto fun _=>0))) (.goto fun _=>1))
  | 1=>.pop 0 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.isSome)
      (.push 2 (fun _=>true) (.goto fun _=>1))
      (.load (fun v=>(none,v.2)) (.branch (fun v=>v.2) (.goto fun _=>2) (.goto fun _=>4))))
  | 2=>.pop 1 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.isSome)
      (.pop 2 (fun v _=>(none,v.2)) (.goto fun _=>2)) (.goto fun _=>3))
  | 3=>.pop 2 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.isSome)
      (.push 3 (fun _=>true) (.goto fun _=>3)) (.load (fun _=>reset) .halt))
  | _=>.pop 2 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.isSome)
      (.goto fun _=>4) (.load (fun _=>reset) .halt))
/-- Actual fixed finite machine for the proved instruction closure. -/
def machine : Machine where
  K:=Fin 4;input:=0;output:=3;Λ:=Fin 5;main:=0;σ:=Var;initial:=reset;program:=program

/-- Complete configuration with all tapes, finite label and variables. -/
def cfg (l:Fin 5) (s a q d:List Bool) (v:Var) :
    TM2.Cfg (fun _:Fin 4=>Bool) (Fin 5) Var := ⟨some l,v,![s,a,q,d]⟩
/-- Complete clean halt with only output populated and the finite flag reset. -/
def halt (d:List Bool) : TM2.Cfg (fun _:Fin 4=>Bool) (Fin 5) Var :=
  ⟨none,reset,![[],[],[],d]⟩

/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem parseA_cons (s a q d:List Bool) (v:Var) :
    TM2.step program (cfg 0 (true::s) a q d v)=some (cfg 0 s (true::a) q d (some true,true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem parseA_sep (s a q d:List Bool) (v:Var) :
    TM2.step program (cfg 0 (false::s) a q d v)=some (cfg 1 s a q d (some false,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem parseQ_cons (s a q d:List Bool) (v:Var) :
    TM2.step program (cfg 1 (true::s) a q d v)=some (cfg 1 s a (true::q) d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem parseQ_nil (a q d:List Bool) (v:Var) :
    TM2.step program (cfg 1 [] a q d v)=some (cfg (if v.2 then 2 else 4) [] a q d (none,v.2)) := by
  cases hv:v.2 <;> simp [TM2.step,program,cfg,TM2.stepAux,hv,TM2.Cfg.mk.injEq]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem cancel_cons (a q d:List Bool) (v:Var) :
    TM2.step program (cfg 2 [] (true::a) (true::q) d v)=some (cfg 2 [] a q d (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem cancel_nil (q d:List Bool) (v:Var) :
    TM2.step program (cfg 2 [] [] q d v)=some (cfg 3 [] [] q d (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem copy_cons (q d:List Bool) (v:Var) :
    TM2.step program (cfg 3 [] [] (true::q) d v)=some (cfg 3 [] [] q (true::d) (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem copy_nil (d:List Bool) (v:Var) :
    TM2.step program (cfg 3 [] [] [] d v)=some (halt d) := by
  simp [TM2.step,program,cfg,halt,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem drain_cons (q d:List Bool) (v:Var) :
    TM2.step program (cfg 4 [] [] (true::q) d v)=some (cfg 4 [] [] q d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem drain_nil (d:List Bool) (v:Var) :
    TM2.step program (cfg 4 [] [] [] d v)=some (halt d) := by
  simp [TM2.step,program,cfg,halt,reset,TM2.stepAux,TM2.Cfg.mk.injEq]

/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem runA (a:ℕ) (s b q d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[a+1]
      (some (cfg 0 (unary a++false::s) b q d v))=
      some (cfg 1 s (unary a++b) q d (some false,v.2 || decide (0<a))) := by
  induction a generalizing b v with
  | zero=>simp [unary,parseA_sep]
  | succ a ih=>
    simp only [unary_succ,List.cons_append]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,parseA_cons]
    rw [ih];simp [unary_append_cons]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem runQ (q:ℕ) (a b d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[q+1]
      (some (cfg 1 (unary q) a b d v))=
      some (cfg (if v.2 then 2 else 4) [] a (unary q++b) d (none,v.2)) := by
  induction q generalizing b v with
  | zero=>simp [unary,parseQ_nil]
  | succ q ih=>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,parseQ_cons]
    rw [ih];simp [unary_append_cons]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem runCancel (a r:ℕ) (d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[a+1]
      (some (cfg 2 [] (unary a) (unary (a+r)) d v))=
      some (cfg 3 [] [] (unary r) d (none,v.2)) := by
  induction a generalizing v with
  | zero=>simp [unary,cancel_nil]
  | succ a ih=>
    rw [show a+1+r=(a+r)+1 by omega]
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,cancel_cons]
    exact ih (none,v.2)
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem runCopy (q:ℕ) (d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[q+1]
      (some (cfg 3 [] [] (unary q) d v))=some (halt (unary q++d)) := by
  induction q generalizing d v with
  | zero=>simp [unary,copy_nil]
  | succ q ih=>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,copy_cons]
    rw [ih];simp [unary_append_cons]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem runDrain (q:ℕ) (d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[q+1]
      (some (cfg 4 [] [] (unary q) d v))=some (halt d) := by
  induction q generalizing v with
  | zero=>simp [unary,drain_nil]
  | succ q ih=>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,drain_cons]
    exact ih (some true,v.2)

/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem parseRun (a q:ℕ) :
    (fun c=>c.bind (TM2.step program))^[a+q+2]
      (some (cfg 0 (pairInput a q) [] [] [] reset))=
      some (cfg (if decide (0<a) then 2 else 4) [] (unary a) (unary q) [] (none,decide (0<a))) := by
  rw [show a+q+2=(q+1)+(a+1) by omega,Function.iterate_add_apply]
  simp only [pairInput]
  rw [runA]
  simp only [reset,Bool.false_or,List.append_nil]
  simpa only [List.append_nil] using runQ q (unary a) [] [] (some false,decide (0<a))

/-- Mathematical specification of the emitted result; never a program callback. -/
def output (a q:ℕ) : ℕ := if a=0 then 0 else q-a
/-- Exact actual count, distinguishing zero cleanup from nonzero cancellation. -/
def steps (a q:ℕ) : ℕ := if a=0 then 2*q+3 else a+2*q+4

/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem init_eq (a q:ℕ) : machine.init (pairInput a q)=cfg 0 (pairInput a q) [] [] [] reset := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem halt_eq (y:List Bool) : halt y=machine.halt y := by
  simp [halt,Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]

/-- Complete actual counted execution, including clean halt. -/
theorem run (a q:ℕ) (haq:a≤q) :
    (fun c=>c.bind (TM2.step machine.program))^[steps a q]
      (some (machine.init (pairInput a q)))=some (machine.halt (unary (output a q))) := by
  rw [init_eq,←halt_eq]
  change (fun c=>c.bind (TM2.step program))^[steps a q]
    (some (cfg 0 (pairInput a q) [] [] [] reset))=_
  by_cases ha:a=0
  · subst a
    rw [show steps 0 q=(q+1)+(0+q+2) by simp only [steps,↓reduceIte];omega,
      Function.iterate_add_apply,parseRun]
    simp only [Nat.lt_irrefl,decide_false,Bool.false_eq_true,↓reduceIte,unary_zero]
    rw [runDrain]
    simp [output,unary]
    rfl
  · have hap:0<a:=by omega
    rw [show steps a q=((q-a+1)+(a+1))+(a+q+2) by simp only [steps,ha,↓reduceIte];omega,
      Function.iterate_add_apply,parseRun]
    simp only [hap,decide_true,↓reduceIte]
    rw [Function.iterate_add_apply]
    have hqa:q=a+(q-a):=by omega
    have hc:=runCancel a (q-a) [] (none,true)
    rw [←hqa] at hc
    rw [hc,runCopy]
    simp [output,ha]
    rfl

/-- Whole actual execution certificate assembled from proved tape runs. -/
def exec (a q:ℕ) (haq:a≤q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (pairInput a q))
      (some (machine.halt (unary (output a q)))) (steps a q) :=
  ⟨⟨steps a q,run a q haq⟩,le_refl _⟩

/-- Proved actual execution phase or structural tape invariant for the complete program. -/
theorem steps_le (a q:ℕ) : steps a q≤3*((pairInput a q).length+1) := by
  rw [pairInput_length]
  by_cases ha:a=0 <;> simp only [steps,ha,↓reduceIte] <;> omega
/-- Linear polynomial derived from complete actual executions and tape lengths. -/
noncomputable def time : Polynomial ℕ := Polynomial.C 3*(Polynomial.X+1)
/-- Whole actual clean execution at the derived input-length polynomial budget. -/
noncomputable def polyExec (a q:ℕ) (haq:a≤q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (pairInput a q))
      (some (machine.halt (unary (output a q)))) (time.eval (pairInput a q).length) := by
  have h:=exec a q haq
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simpa [time] using steps_le a q

/-- Actual cancellation output equals the true canonical ZMod negative. -/
theorem output_eq_neg (a q:ℕ) (hq:0<q) (haq:a<q) : output a q=(-(a:ZMod q)).val := by
  let : NeZero q:=⟨hq.ne'⟩
  have he:((a:ZMod q)=0)↔a=0 := by
    rw [←ZMod.val_eq_zero (a:ZMod q),ZMod.val_natCast_of_lt haq]
  simp only [output,ZMod.neg_val,he,ZMod.val_natCast_of_lt haq]

/-- Standard Mathlib output certificate from the whole actual program. -/
noncomputable def outputsInTime (a q:ℕ) (haq:a≤q) :
    TM2OutputsInTime machine.toFinTM2 (pairInput a q) (some (unary (output a q)))
      (time.eval (pairInput a q).length) := Machine.outputsInTime machine _ _ _ (polyExec a q haq)
/-- The actual output is the true canonical finite-field negative. -/
noncomputable def outputsZModInTime (a q:ℕ) (hq:0<q) (haq:a<q) :
    TM2OutputsInTime machine.toFinTM2 (pairInput a q) (some (unary (-(a:ZMod q)).val))
      (time.eval (pairInput a q).length) := by
  have h:=outputsInTime a q haq.le
  rw [output_eq_neg a q hq haq] at h;exact h

/-- Canonical positive-modulus input facts; no answer, execution or cost fields. -/
def Domain := {x:ℕ×ℕ+//x.1<x.2.val}
/-- Faithful encoding of the original operands and modulus. -/
def input (x:Domain) := pairInput x.val.1 x.val.2.val

/-- The encoded input distinguishes every non-proof domain parameter. -/
theorem input_injective : Function.Injective input := by
  intro x y h
  have he:=@pairInput_injective (x.val.1,x.val.2.val) (y.val.1,y.val.2.val) h
  have ha:x.val.1=y.val.1:=congrArg (fun z:ℕ×ℕ=>z.1) he
  have hq:x.val.2.val=y.val.2.val:=congrArg (fun z:ℕ×ℕ=>z.2) he
  exact Subtype.ext (Prod.ext ha (Subtype.ext hq))

/-- Standard polynomial-time certificate using the actual machine and faithful input. -/
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary
    (fun x:Domain=>output x.val.1 x.val.2.val) where
  tm:=machine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary (output x.val.1 x.val.2.val)))) (time.eval (input x).length)
    have h:=outputsInTime x.val.1 x.val.2.val x.property.le
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input] using h

end QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation
