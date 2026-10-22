import QEC.Coding.BitTuring.Composition

/-!
# Actual arbitrary Boolean delimiter and reversal programs

A literal false header followed by two genuine copy loops preserves every payload bit and
appends a field delimiter. A separate one-loop machine reverses the complete bit string. Both
complete counted runs clear all auxiliary tapes. These are concrete finite instructions.
-/

namespace QEC.Coding.BitTuring.BitDelimiter
open Turing StateTransition
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
abbrev Label := Unit⊕Bool
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
abbrev Statement := TM2.Stmt (fun _:Fin 3=>Bool) Label (Option Bool)
/-- Actual finite Boolean instructions; varying integers occur only on tapes. -/
def program : Label→Statement
  | .inl _=>.push 2 (fun _=>false) (.goto fun _=>.inr true)
  | .inr l=>liftStatement id Sum.inr id (fun _ w=>w) none (copyProgram l)
/-- Actual fixed finite machine for the proved instruction closure. -/
def machine : Machine where
  K:=Fin 3;input:=0;output:=2;Λ:=Label;main:=.inl ();σ:=Option Bool;initial:=none;program:=program

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
def embed : TM2.Cfg (fun _:Fin 3=>Bool) Bool (Option Bool)→
    TM2.Cfg (fun _:Fin 3=>Bool) Label (Option Bool) := liftCfg Sum.inr id id none

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem stepAuxCopy (l:Bool) (v:Option Bool) (S:Fin 3→List Bool) :
    TM2.stepAux (program (.inr l)) v S=embed (TM2.stepAux (copyProgram l) v S) :=
  stepAux_liftStatement (K:=Fin 3) (K':=Fin 3) (Λ:=Bool) (Λ':=Label)
    (σ:=Option Bool) (σ':=Option Bool) id Sum.inr id (fun _ w=>w) none id id
    (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _ _=>rfl) (copyProgram l) v S

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem stepCopy (c c':TM2.Cfg (fun _:Fin 3=>Bool) Bool (Option Bool))
    (h:TM2.step copyProgram c=some c') : TM2.step program (embed c)=some (embed c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none=>simp [TM2.step] at h
  | some l=>
    have hh:TM2.stepAux (copyProgram l) v S=c':=Option.some.inj h
    rw [←hh];exact congrArg some (stepAuxCopy l v S)

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
def startCfg (w:List Bool) : TM2.Cfg (fun _:Fin 3=>Bool) Label (Option Bool) :=
  ⟨some (.inl ()),none,![w,[],[]]⟩
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem init_eq (w:List Bool) : machine.init w=startCfg w := by
  simp [Machine.init,machine,startCfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem header (w:List Bool) : TM2.step program (startCfg w)=
    some (embed (copyCfg true w [] [false] none)) := by
  simp [program,startCfg,embed,liftCfg,copyCfg,TM2.step,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem halt_eq (y:List Bool) : embed (copyHalt y)=machine.halt y := by
  simp [embed,liftCfg,copyHalt,Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]

/-- Complete counted actual execution certificate. -/
def exec (w:List Bool) : EvalsToInTime (TM2.step machine.program) (machine.init w)
    (some (machine.halt (w++[false]))) (2*w.length+3) := by
  have hc:(fun c=>c.bind (TM2.step copyProgram))^[2*w.length+2]
      (some (copyCfg true w [] [false] none))=some (copyHalt (w++[false])) := by
    rw [show 2*w.length+2=(w.reverse.length+1)+(w.length+1) by simp;omega,
      Function.iterate_add_apply,copyRun_source]
    simp only [List.append_nil]
    rw [copyRun_buffer,List.reverse_reverse]
  refine ⟨⟨2*w.length+3,?_⟩,le_refl _⟩
  rw [init_eq]
  change (fun c=>c.bind (TM2.step program))^[2*w.length+3] (some (startCfg w))=_
  rw [show 2*w.length+3=(2*w.length+2)+1 by omega,Function.iterate_add_apply]
  simp only [Function.iterate_one,Option.bind_some]
  rw [header]
  have h:=iterate_lift (TM2.step copyProgram) (TM2.step program) embed stepCopy _ _ _ hc
  rw [halt_eq] at h;exact h

end QEC.Coding.BitTuring.BitDelimiter
namespace QEC.Coding.BitTuring.BitReverse
open Turing StateTransition
/-- Actual fixed finite machine for the proved instruction closure. -/
def machine : Machine where
  K:=Fin 3;input:=1;output:=2;Λ:=Bool;main:=false;σ:=Option Bool;initial:=none;program:=copyProgram

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem init_eq (w:List Bool) : machine.init w=copyCfg false [] w [] none := by
  simp [Machine.init,machine,copyCfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem halt_eq (y:List Bool) : copyHalt y=machine.halt y := by
  simp [Machine.halt,machine,copyHalt,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]

/-- Complete counted actual execution certificate. -/
def exec (w:List Bool) : EvalsToInTime (TM2.step machine.program) (machine.init w)
    (some (machine.halt w.reverse)) (w.length+1) := by
  have h:=copyRun_buffer w [] none
  rw [List.append_nil,halt_eq,←init_eq] at h
  exact ⟨⟨w.length+1,h⟩,le_refl _⟩

end QEC.Coding.BitTuring.BitReverse
