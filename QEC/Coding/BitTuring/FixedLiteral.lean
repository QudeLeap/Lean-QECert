import QEC.Coding.BitTuring.RetainedInput

/-!
# Actual fixed Boolean literal and retained prefix programs

A compile-time Boolean list becomes a finite tree of literal push instructions. The actual
incoming-input scan drains every bit; the tree writes the original literal order and resets
finite control. Complete transition/count/clean-halt proofs and standard certificates follow.
A real input-retention compiler emits literal++original input with its full transfer cost.
The fixed tree depends only on fixed construction parameters; varying values occur on tapes.
Time is measured in the existing Mathlib TM2 transition model, with fixed code size.
-/

namespace QEC.Coding.BitTuring.FixedLiteral
open Turing StateTransition
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
abbrev Statement := TM2.Stmt (fun _:Fin 2=>Bool) Bool (Option Bool)
/-- The list is compiled into a fixed finite instruction tree, before varying input arrives. -/
def write : List Bool → Statement
  | []=>.load (fun _=>none) .halt
  | b::bs=>.push 1 (fun _=>b) (write bs)
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
def program (w:List Bool) : Bool→Statement
  | true=>.pop 0 (fun _ h=>h) (.branch (fun h=>h.isSome)
      (.goto fun _=>true) (.goto fun _=>false))
  | false=>write w.reverse
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
def machine (w:List Bool) : Machine where
  K:=Fin 2;input:=0;output:=1;Λ:=Bool;main:=true;σ:=Option Bool;initial:=none;program:=program w
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
def cfg (l:Bool) (s d:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 2=>Bool) Bool (Option Bool) := ⟨some l,v,![s,d]⟩
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
theorem push_tapes (s d:List Bool) (b:Bool) :
    Function.update (![s,d]:Fin 2→List Bool) 1 (b::d)=![s,b::d] := by
  funext k;fin_cases k <;> simp [Function.update]
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
theorem write_aux (w s d:List Bool) (v:Option Bool) :
    TM2.stepAux (write w) v ![s,d]=⟨none,none,![s,w.reverse++d]⟩ := by
  induction w generalizing d v with
  | nil=>simp [write,TM2.stepAux]
  | cons b bs ih=>
      simp only [write,TM2.stepAux,Matrix.cons_val_one,Matrix.cons_val_zero,push_tapes]
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih (b::d) v

/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
theorem drain_cons (w:List Bool) (b:Bool) (s d:List Bool) (v:Option Bool) :
    TM2.step (program w) (cfg true (b::s) d v)=some (cfg true s d (some b)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
theorem drain_nil (w d:List Bool) (v:Option Bool) :
    TM2.step (program w) (cfg true [] d v)=some (cfg false [] d none) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
theorem drain_run (w s d:List Bool) (v:Option Bool) :
    (fun c=>c.bind (TM2.step (program w)))^[s.length+1] (some (cfg true s d v))=
      some (cfg false [] d none) := by
  induction s generalizing v with
  | nil=>simp [drain_nil]
  | cons b bs ih=>
      rw [List.length_cons,Nat.add_right_comm,Function.iterate_succ_apply]
      simp only [Option.bind_some,drain_cons]
      exact ih (some b)
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
theorem init_eq (w s:List Bool) : (machine w).init s=cfg true s [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
theorem emit (w:List Bool) : TM2.step (program w) (cfg false [] [] none)=
    some ((machine w).halt w) := by
  simp only [TM2.step,cfg,program,write_aux,List.reverse_reverse,List.append_nil]
  simp [Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
def exec (w s:List Bool) : EvalsToInTime (TM2.step (machine w).program) ((machine w).init s)
    (some ((machine w).halt w)) (s.length+2) := by
  refine ⟨⟨s.length+2,?_⟩,le_refl _⟩
  rw [init_eq]
  change (fun c=>c.bind (TM2.step (program w)))^[s.length+2] (some (cfg true s [] none))=_
  rw [show s.length+2=1+(s.length+1) by omega,Function.iterate_add_apply,drain_run]
  simp only [Function.iterate_one,Option.bind_some,emit]
  rfl
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def time : Polynomial ℕ := Polynomial.X+Polynomial.C 2
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def polyExec (w s:List Bool) : EvalsToInTime (TM2.step (machine w).program)
    ((machine w).init s) (some ((machine w).halt w)) (time.eval s.length) := by
  simpa only [time,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using exec w s
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def computableInPolyTime (w:List Bool) : TM2ComputableInPolyTime id id (fun _:List Bool=>w) where
  tm:=(machine w).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun s=>by
    change TM2OutputsInTime (machine w).toFinTM2 (List.map id s) (some (List.map id w)) (time.eval s.length)
    have h:=Machine.outputsInTime (machine w) _ _ _ (polyExec w s)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h

/-- Actual input duplication and literal writing emits this fixed header before original input. -/
def prefixMachine (w:List Bool) := RetainedInput.machine (machine w)
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def prefixTime (w:List Bool) : Polynomial ℕ :=
  Polynomial.C 4*Polynomial.X+Polynomial.C (2*w.length+8)
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def prefixExec (w s:List Bool) :
    EvalsToInTime (TM2.step (prefixMachine w).program) ((prefixMachine w).init s)
      (some ((prefixMachine w).halt (w++s))) ((prefixTime w).eval s.length) := by
  have h:=RetainedInput.executes (machine w) s w _ (exec w s)
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simp only [prefixTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega
end QEC.Coding.BitTuring.FixedLiteral
