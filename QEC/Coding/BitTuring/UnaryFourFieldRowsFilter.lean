import QEC.Coding.BitTuring.UnaryPrefixProjection
import QEC.Coding.BitTuring.FixedLiteral
import QEC.Coding.BitTuring.UnaryFieldProjection

/-!
# Actual finite four-field row-filter controller

The finite controller lifts a concrete retained query, preserves the reverse accepted-bit buffer on a disjoint tape, parses its own computed flag and four row fields, and restores the remaining source in original order. Real EOF drains the header, drops the final separator, reverses the buffer, resets all variables and halts cleanly. These are compiler/phase lemmas; the source-level consumer supplies the proved concrete PSL search program, not an answer oracle.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
abbrev Stack:=P.K⊕Fin 3
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
abbrev Label:=P.Λ⊕Fin 15
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
abbrev Var:=P.σ×Bool×Option Bool
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
abbrev Statement:=TM2.Stmt (fun _:Stack P=>Bool) (Label P) (Var P)
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
def setHead (v:Var P) (h:Option Bool):Var P:=(v.1,v.2.1,h)
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
def scan (k:Fin 15) (source:Stack P) (next:Fin 15) (save:Bool):Statement P:=
 .pop source (setHead P) (if save then
  .push (.inr 0) (fun v=>v.2.2.getD false)
   (.branch (fun v=>v.2.2.getD false) (.goto fun _=>.inr k) (.goto fun _=>.inr next))
  else .branch (fun v=>v.2.2.getD false) (.goto fun _=>.inr k) (.goto fun _=>.inr next))
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
def program:Label P→Statement P
 | .inl l=>liftStatement Sum.inl Sum.inl Prod.fst (fun v w=>(w,v.2))
   (some (.inr 3)) (P.program l)
 | .inr k=>
  if k=0 then scan P 0 (.inl P.input) 1 true
  else if k=1 then .peek (.inl P.input) (setHead P)
   (.branch (fun v=>v.2.2.isSome) (.goto fun _=>.inr 2) (.goto fun _=>.inr 12))
  else if k=2 then .pop (.inr 0) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inl P.input) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 2))
   (.load (fun _=>(P.initial,false,none)) (.goto fun _=>.inl P.main)))
  else if k=3 then .pop (.inl P.output) (fun v h=>(v.1,h.getD false,h)) (.goto fun _=>.inr 4)
  else if k=4 then scan P 4 (.inl P.output) 5 true
  else if hk:5≤k.val ∧ k.val≤8 then
   .pop (.inl P.output) (setHead P)
    (.branch (fun v=>v.2.1)
     (.branch (fun v=>v.2.2.getD false) (.goto fun _=>.inr k)
      (.goto fun _=>.inr ⟨k.val+1,by omega⟩))
     (.push (.inr 1) (fun v=>v.2.2.getD false)
      (.branch (fun v=>v.2.2.getD false) (.goto fun _=>.inr k)
       (.goto fun _=>.inr ⟨k.val+1,by omega⟩))))
  else if k=9 then .pop (.inl P.output) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inr 2) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 9)) (.goto fun _=>.inr 10))
  else if k=10 then .pop (.inr 2) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inl P.input) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 10)) (.goto fun _=>.inr 11))
  else if k=11 then .pop (.inr 0) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inl P.input) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 11))
   (.load (fun _=>(P.initial,false,none)) (.goto fun _=>.inr 0)))
  else if k=12 then .pop (.inr 0) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.goto fun _=>.inr 12) (.goto fun _=>.inr 13))
  else if k=13 then .pop (.inr 1) (setHead P) (.goto fun _=>.inr 14)
  else .pop (.inr 1) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inl P.output) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 14))
   (.load (fun _=>(P.initial,false,none)) .halt))
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
def machine:Machine where
 K:=Stack P;input:=.inl P.input;output:=.inl P.output;Λ:=Label P;main:=.inr 0
 σ:=Var P;initial:=(P.initial,false,none);program:=program P
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
def cfg (k:Fin 15) (f:Bool) (h:Option Bool) (I O H C B:List Bool):TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P):=
 ⟨some (.inr k),(P.initial,f,h),fun j=>match j with
 | .inl j=>DrainInput.tapes P I O j
 | .inr j=>![H,C,B] j⟩
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
def bodyTapes (C:List Bool) (S:P.K→List Bool):Stack P→List Bool
 | .inl j=>S j
 | .inr j=>![[],C,[]] j
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
def embedBody (C:List Bool):P.Cfg→TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P):=
 liftCfg Sum.inl (fun v=>(v,false,none)) (bodyTapes P C) (some (.inr 3))
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem bodyTapes_update (C:List Bool) (S:P.K→List Bool) (k:P.K) (w:List Bool):
 Function.update (bodyTapes P C S) (.inl k) w=bodyTapes P C (Function.update S k w):=by
 funext j;cases j with
 |inl j=>by_cases hj:j=k <;>simp [bodyTapes,Function.update,hj]
 |inr j=>simp [bodyTapes,Function.update]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem stepAuxBody (C:List Bool) (l:P.Λ) (v:P.σ) (S:P.K→List Bool):
 TM2.stepAux (program P (.inl l)) (v,false,none) (bodyTapes P C S)=
 embedBody P C (TM2.stepAux (P.program l) v S):=
 stepAux_liftStatement (K:=P.K) (K':=Stack P) (Λ:=P.Λ) (Λ':=Label P)
  (σ:=P.σ) (σ':=Var P) Sum.inl Sum.inl Prod.fst (fun v w=>(w,v.2))
  (some (.inr 3)) (fun v=>(v,false,none)) (bodyTapes P C)
  (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (bodyTapes_update P C) (P.program l) v S
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem stepBody (C:List Bool) (c c':P.Cfg) (h:TM2.step P.program c=some c'):
 TM2.step (machine P).program (embedBody P C c)=some (embedBody P C c'):=by
 rcases c with ⟨l,v,S⟩;cases l with
 |none=>simp [TM2.step] at h
 |some l=>
  have hh:TM2.stepAux (P.program l) v S=c':=Option.some.inj h
  rw [←hh];exact congrArg some (stepAuxBody P C l v S)
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem embed_halt (hio:P.input≠P.output) (C y:List Bool):
 embedBody P C (P.halt y)=cfg P 3 false none [] y [] C []:=by
 simp [embedBody,liftCfg,Machine.halt,cfg,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [bodyTapes,DrainInput.tapes,Function.update,eq_comm]
 |inr j=>simp [bodyTapes]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem q0_bit (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) :
 TM2.step (program P) (cfg P 0 f h (true::I) O H C B)=some (cfg P 0 f (some true) I O (true::H) C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,scan,setHead,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem q0_sep (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) :
 TM2.step (program P) (cfg P 0 f h (false::I) O H C B)=some (cfg P 1 f (some false) I O (false::H) C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,scan,setHead,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem q4_bit (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) :
 TM2.step (program P) (cfg P 4 f h I (true::O) H C B)=some (cfg P 4 f (some true) I O (true::H) C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,scan,setHead,Ne.symm hio,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem q4_sep (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) :
 TM2.step (program P) (cfg P 4 f h I (false::O) H C B)=some (cfg P 5 f (some false) I O (false::H) C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,scan,setHead,Ne.symm hio,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem peek_more (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 1 f h (a::I) O H C B)=some (cfg P 2 f (some a) (a::I) O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem peek_empty (f:Bool) (h:Option Bool) (O H C B:List Bool) :
 TM2.step (program P) (cfg P 1 f h [] O H C B)=some (cfg P 12 f none [] O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem restore2_cons (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 2 f h I O (a::H) C B)=some (cfg P 2 f (some a) (a::I) O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem copy9_cons (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 9 f h I (a::O) H C B)=some (cfg P 9 f (some a) I O H C (a::B)):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,Ne.symm hio,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem copy9_nil (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I H C B:List Bool) :
 TM2.step (program P) (cfg P 9 f h I [] H C B)=some (cfg P 10 f none I [] H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,Ne.symm hio]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem copy10_cons (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 10 f h I O H C (a::B))=some (cfg P 10 f (some a) (a::I) O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem copy10_nil (f:Bool) (h:Option Bool) (I O H C:List Bool) :
 TM2.step (program P) (cfg P 10 f h I O H C [])=some (cfg P 11 f none I O H C []):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem restore11_cons (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 11 f h I O (a::H) C B)=some (cfg P 11 f (some a) (a::I) O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem restore11_nil (f:Bool) (h:Option Bool) (I O C B:List Bool) :
 TM2.step (program P) (cfg P 11 f h I O [] C B)=some (cfg P 0 false none I O [] C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem drain12_cons (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 12 f h I O (a::H) C B)=some (cfg P 12 f (some a) I O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem drain12_nil (f:Bool) (h:Option Bool) (I O C B:List Bool) :
 TM2.step (program P) (cfg P 12 f h I O [] C B)=some (cfg P 13 f none I O [] C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem drop13 (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) :
 TM2.step (program P) (cfg P 13 f h I O H C B)=some (cfg P 14 f C.head? I O H C.tail B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem reverse14_cons (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 14 f h I O H (a::C) B)=some (cfg P 14 f (some a) I (a::O) H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,Ne.symm hio,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem flag3 (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 3 f h I (a::O) H C B)=some (cfg P 4 a (some a) I O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,Ne.symm hio,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem restore2_nil (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I C:List Bool) :
 TM2.step (program P) (cfg P 2 f h I [] [] C [])=some (embedBody P C (P.init I)):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,embedBody,liftCfg,Machine.init,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm,bodyTapes]
 |inr j=>fin_cases j <;>simp [Function.update,bodyTapes]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem reverse14_nil (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (O:List Bool) :
 TM2.step (program P) (cfg P 14 f h [] O [] [] [])=some ((machine P).halt O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,machine,Machine.halt,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem field_bit (hio:P.input≠P.output) (k:Fin 4) (f:Bool) (h:Option Bool)
 (I O H C B:List Bool):
 TM2.step (program P) (cfg P ⟨5+k.val,by omega⟩ f h I (true::O) H C B)=
 some (cfg P ⟨5+k.val,by omega⟩ f (some true) I O H (if f then C else true::C) B):=by
 fin_cases k <;> cases f
 all_goals simp [TM2.step,program,cfg,setHead,TM2.stepAux,DrainInput.tapes,Ne.symm hio,TM2.Cfg.mk.injEq]
 all_goals funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem field_sep (hio:P.input≠P.output) (k:Fin 4) (f:Bool) (h:Option Bool)
 (I O H C B:List Bool):
 TM2.step (program P) (cfg P ⟨5+k.val,by omega⟩ f h I (false::O) H C B)=
 some (cfg P ⟨6+k.val,by omega⟩ f (some false) I O H (if f then C else false::C) B):=by
 fin_cases k <;> cases f
 all_goals simp [TM2.step,program,cfg,setHead,TM2.stepAux,DrainInput.tapes,Ne.symm hio,TM2.Cfg.mk.injEq]
 all_goals funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem q0_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (q:ℕ) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[q+1] (some (cfg P 0 f h (unary q++false::I) O H C B))=
 some (cfg P 1 f (some false) I O ((unary q++[false]).reverse++H) C B):=by
 induction q generalizing h H with
 |zero=>simpa [unary] using q0_sep P hio f h I O H C B
 |succ q ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,q0_bit P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem q4_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (q:ℕ) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[q+1] (some (cfg P 4 f h I (unary q++false::O) H C B))=
 some (cfg P 5 f (some false) I O ((unary q++[false]).reverse++H) C B):=by
 induction q generalizing h H with
 |zero=>simpa [unary] using q4_sep P hio f h I O H C B
 |succ q ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,q4_bit P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem restore2_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I H C:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[H.length+1] (some (cfg P 2 f h I [] H C []))=
 some (embedBody P C (P.init (H.reverse++I))):=by
 induction H generalizing h I with
 |nil=>simpa using restore2_nil P hio f h I C
 |cons a H ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,restore2_cons P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem copy9_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[O.length+1] (some (cfg P 9 f h I O H C B))=
 some (cfg P 10 f none I [] H C (O.reverse++B)):=by
 induction O generalizing h B with
 |nil=>simpa using copy9_nil P hio f h I H C B
 |cons a O ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,copy9_cons P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem copy10_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[B.length+1] (some (cfg P 10 f h I O H C B))=
 some (cfg P 11 f none (B.reverse++I) O H C []):=by
 induction B generalizing h I with
 |nil=>simpa using copy10_nil P f h I O H C
 |cons a B ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,copy10_cons P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem restore11_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[H.length+1] (some (cfg P 11 f h I O H C B))=
 some (cfg P 0 false none (H.reverse++I) O [] C B):=by
 induction H generalizing h I with
 |nil=>simpa using restore11_nil P f h I O C B
 |cons a H ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,restore11_cons P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem drain12_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[H.length+1] (some (cfg P 12 f h I O H C B))=
 some (cfg P 13 f none I O [] C B):=by
 induction H generalizing h with
 |nil=>simpa using drain12_nil P f h I O C B
 |cons a H ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,drain12_cons P hio]
  exact ih (some a)
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem reverse14_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (O C:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[C.length+1] (some (cfg P 14 f h [] O [] C []))=
 some ((machine P).halt (C.reverse++O)):=by
 induction C generalizing h O with
 |nil=>simpa using reverse14_nil P hio f h O
 |cons a C ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,reverse14_cons P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  rfl
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
def pushed (f:Bool) (w C:List Bool):List Bool:=if f then C else w.reverse++C
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem pushed_append (f:Bool) (u v C:List Bool):pushed f (u++v) C=pushed f v (pushed f u C):=by
 cases f <;>simp [pushed,List.reverse_append,List.append_assoc]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem field_run (hio:P.input≠P.output) (k:Fin 4) (f:Bool) (h:Option Bool) (a:ℕ)
 (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[a+1]
  (some (cfg P ⟨5+k.val,by omega⟩ f h I (unary a++false::O) H C B))=
 some (cfg P ⟨6+k.val,by omega⟩ f (some false) I O H (pushed f (unary a++[false]) C) B):=by
 induction a generalizing h C with
 |zero=>simpa [unary,pushed] using field_sep P hio k f h I O H C B
 |succ a ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,field_bit P hio]
  rw [ih]
  cases f <;>simp [pushed,List.reverse_cons,List.append_assoc]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem parse4_run (hio:P.input≠P.output) (xs:List ℕ) (k:Fin 5) (hk:k.val+xs.length=4)
 (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[(stream xs).length]
  (some (cfg P ⟨5+k.val,by omega⟩ f h I (stream xs++O) H C B))=
 some (cfg P 9 f (if xs=[] then h else some false) I O H (pushed f (stream xs) C) B):=by
 induction xs generalizing k h C with
 |nil=>
  have he:⟨5+k.val,by omega⟩=(9:Fin 15):=by
   apply Fin.ext;change 5+k.val=9;simp only [List.length_nil] at hk;omega
  simp [stream,pushed,he]
 |cons a xs ih=>
  have hl:k.val<4:=by simp only [List.length_cons] at hk;omega
  let j:Fin 5:=⟨k.val+1,by omega⟩
  let kk:Fin 4:=⟨k.val,hl⟩
  have ht:=ih j (by dsimp [j];simp only [List.length_cons] at hk;omega) (some false)
   (pushed f (unary a++[false]) C)
  have hs:(stream (a::xs)).length=(stream xs).length+(a+1):=by
   simp only [stream,List.length_append,List.length_cons,unary_length];omega
  rw [hs,Function.iterate_add_apply]
  have he:stream (a::xs)++O=unary a++false::(stream xs++O):=by
   simp only [stream,List.append_assoc,List.cons_append]
  rw [he]
  have hf:=field_run P hio kk f h a I (stream xs++O) H C B
  have hj:(⟨6+kk.val,by omega⟩:Fin 15)=⟨5+j.val,by omega⟩:=by apply Fin.ext;dsimp [kk,j];omega
  change (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[a+1]
   (some (cfg P ⟨5+k.val,by omega⟩ f h I (unary a++false::(stream xs++O)) H C B))=_ at hf
  rw [hf,hj,ht]
  have hp:pushed f (stream (a::xs)) C=pushed f (stream xs) (pushed f (unary a++[false]) C):=by
   rw [show stream (a::xs)=(unary a++[false])++stream xs by simp [stream,List.append_assoc],pushed_append]
  rw [hp]
  cases xs <;>simp
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
abbrev next:=fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P))
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
def qword (q:ℕ):List Bool:=unary q++[false]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem qword_length (q:ℕ):(qword q).length=q+1:=by simp [qword,unary_length]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem qword_stream (q:ℕ):qword q=stream [q]:=by simp [qword,stream]
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem entry_run (hio:P.input≠P.output) (q:ℕ) (s C:List Bool) (hs:s≠[]):
 (next P)^[2*(q+1)+2] (some (cfg P 0 false none (qword q++s) [] [] C []))=
 some (embedBody P C (P.init (qword q++s))):=by
 cases s with
 |nil=>exact (hs rfl).elim
 |cons a s=>
  rw [show 2*(q+1)+2=((qword q).reverse.length+1)+1+(q+1) by rw [List.length_reverse,qword_length];omega,
   Function.iterate_add_apply]
  have hq:=q0_run P hio false none q (a::s) [] [] C []
  have hw:qword q++a::s=unary q++false::(a::s):=by simp [qword,List.append_assoc]
  rw [hw,hq]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply,Function.iterate_one]
  simp only [Option.bind_some,peek_more P]
  simpa only [qword,List.reverse_reverse,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using
   restore2_run P hio false (some a) (a::s) (qword q).reverse C
/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem body_run (C x y:List Bool) (n:ℕ)
 (hn:(fun c=>c.bind (TM2.step P.program))^[n] (some (P.init x))=some (P.halt y)):
 (next P)^[n] (some (embedBody P C (P.init x)))=some (embedBody P C (P.halt y)):=
 iterate_lift (TM2.step P.program) (TM2.step (program P)) (embedBody P C)
  (stepBody P C) n _ _ hn

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem parse_current_run (hio:P.input≠P.output) (f:Bool) (q:ℕ) (xs:List ℕ)
 (hxs:xs.length=4) (R C:List Bool):
 (next P)^[(stream xs).length+(q+1)+1]
  (some (cfg P 3 false none [] (f::(qword q++stream xs++R)) [] C []))=
 some (cfg P 9 f (some false) [] R (qword q).reverse (pushed f (stream xs) C) []):=by
 rw [Function.iterate_add_apply,Function.iterate_one]
 simp only [Option.bind_some,flag3 P hio]
 rw [Function.iterate_add_apply]
 have hq:=q4_run P hio f (some f) q [] (stream xs++R) [] C []
 have hw:qword q++stream xs++R=unary q++false::(stream xs++R):=by simp [qword,List.append_assoc]
 rw [hw,hq]
 simp only [List.append_nil]
 have hp:=parse4_run P hio xs 0 (by simpa using hxs) f (some false) [] R (qword q).reverse C []
 have hx:xs≠[]:=by intro he;simp [he] at hxs
 simpa [hx,qword] using hp

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem after_run (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (q:ℕ) (R C:List Bool):
 (next P)^[2*R.length+(q+1)+3]
  (some (cfg P 9 f h [] R (qword q).reverse C []))=
 some (cfg P 0 false none (qword q++R) [] [] C []):=by
 rw [show 2*R.length+(q+1)+3=((qword q).reverse.length+1)+(R.reverse.length+1)+(R.length+1) by
  rw [List.length_reverse,List.length_reverse,qword_length];omega,
  Function.iterate_add_apply,copy9_run P hio]
 simp only [List.append_nil]
 rw [Function.iterate_add_apply,copy10_run P hio]
 simp only [List.reverse_reverse,List.append_nil]
 rw [restore11_run P hio]
 simp only [List.reverse_reverse]

/-- Actual row-controller instruction, tape simulation, field phase or exact counted transfer. -/
theorem empty_run (hio:P.input≠P.output) (q:ℕ) (C:List Bool):
 (next P)^[2*(q+1)+C.tail.length+4]
  (some (cfg P 0 false none (qword q) [] [] C []))=
 some ((machine P).halt C.tail.reverse):=by
 rw [show 2*(q+1)+C.tail.length+4=
  (((C.tail.length+1)+1)+((qword q).reverse.length+1))+1+(q+1) by
  rw [List.length_reverse,qword_length];omega,Function.iterate_add_apply]
 have hq:=q0_run P hio false none q [] [] [] C []
 have hw:qword q=unary q++false::([]:List Bool):=by simp [qword]
 rw [hw,hq]
 simp only [List.append_nil]
 rw [Function.iterate_add_apply,Function.iterate_one]
 simp only [Option.bind_some,peek_empty P]
 rw [Function.iterate_add_apply,drain12_run P hio,Function.iterate_add_apply,Function.iterate_one]
 simp only [Option.bind_some,drop13 P hio]
 simpa using reverse14_run P hio false C.head? [] C.tail
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
