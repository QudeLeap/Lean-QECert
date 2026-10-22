import QEC.Coding.BitTuring.UnaryMatrixListQuery
import QEC.Coding.BitTuring.UnaryModularAdjugate

/-!
# Actual retained comparison and finite eight-flag reducer

Real scalar equality executes an actual identity body and comparison loop; actual flag-to-unary
conversion, payload delimiter and input retention preserve every operand. A fixed eight-field
reducer computes the OR of two four-way conjunctions from actual 0/1 unary fields. Every
instruction, phase, cleanup and full stage cost is proved. Flags describe tape data, never an
oracle or a source-machine input. Structural selectors and length invariants are mathematical
specifications, not runtime callbacks.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.PSLComparisonSupport
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection MatrixListQuery
namespace FlagUnary
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def program (_:Unit) : TM2.Stmt (fun _:Fin 2=>Bool) Unit (Option Bool) :=
   .pop 0 (fun _ h=>h) (.branch (fun v=>v.getD false)
     (.push 1 (fun _=>true) (.load (fun _=>none) .halt)) (.load (fun _=>none) .halt))
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def machine : Machine where
  K:=Fin 2;input:=0;output:=1;Λ:=Unit;main:=();σ:=Option Bool;initial:=none;program:=program
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def value (b:Bool) : ℕ := if b then 1 else 0
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem step (b:Bool) : TM2.step machine.program (machine.init [b])=
    some (machine.halt (unary (value b))) :=by
  cases b <;> simp [machine,Machine.init,Machine.halt,TM2.step,program,TM2.stepAux,
    value,unary,Function.update,TM2.Cfg.mk.injEq] <;> (funext k;fin_cases k <;> simp [Function.update])
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def exec (b:Bool) : EvalsToInTime (TM2.step machine.program) (machine.init [b])
    (some (machine.halt (unary (value b)))) 1 :=by
  refine ⟨⟨1,?_⟩,le_refl _⟩
  change (fun c=>c.bind (TM2.step machine.program))^[1] (some (machine.init [b]))=_
  simp only [Function.iterate_one,Option.bind_some,step]
end FlagUnary
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def equalMachine:=UnaryOutputEquality.machine identityMachine
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def equalValue (a b:ℕ) : ℕ :=FlagUnary.value (decide (a=b))
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def equalExec (a b:ℕ) : EvalsToInTime (TM2.step equalMachine.program)
    (equalMachine.init (pairInput a b)) (some (equalMachine.halt [decide (a=b)]))
    (8*(a+b+1)) :=by
  have h:=UnaryOutputEquality.executes identityMachine a b (unary b) (4*(unary b).length+4)
    (identityExec (unary b))
  rw [unary_length] at h
  have he:UnaryOutputEquality.prefixInput a (unary b)=pairInput a b :=rfl
  rw [he] at h
  have hflag:decide (b=a)=decide (a=b) :=by simp only [eq_comm]
  rw [hflag] at h
  exact {h with steps_le_m:=h.steps_le_m.trans (by have hm:max b a≤b+a:=max_le (by omega) (by omega);omega)}
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def equalUnaryMachine:=Composition.machine equalMachine FlagUnary.machine
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def equalUnaryExec (a b:ℕ) : EvalsToInTime (TM2.step equalUnaryMachine.program)
    (equalUnaryMachine.init (pairInput a b)) (some (equalUnaryMachine.halt (unary (equalValue a b))))
    (8*(a+b+1)+5) :=by
  have h:=Composition.executes equalMachine FlagUnary.machine _ _ _ _ _
    (equalExec a b) (FlagUnary.exec (decide (a=b)))
  exact {h with steps_le_m:=h.steps_le_m.trans (by simp only [List.length_singleton];omega)}
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def retainedEquality (n:ℕ) (keep:Fin (n+1)→Bool) := RetainedInput.machine
   (Composition.machine (FieldProjection.machine n keep)
     (Composition.machine equalUnaryMachine UnaryDelimiter.machine))
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 noncomputable def equalityTime : Polynomial ℕ := Polynomial.C 40*(Polynomial.X+1)
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 noncomputable def equalityStageExec (n:ℕ) (keep:Fin (n+1)→Bool) (xs:List ℕ)
    (hx:xs.length=n+1) (a b:ℕ) (hf:fields n keep 0 xs=[a,b]) :
    EvalsToInTime (TM2.step (retainedEquality n keep).program) ((retainedEquality n keep).init (stream xs))
      (some ((retainedEquality n keep).halt (stream (equalValue a b::xs))))
      (equalityTime.eval (stream xs).length) :=by
  have hp:=FieldProjection.polyExec n keep xs hx
  rw [hf,ModularAdjugate.raw_pair] at hp
  have hd:=UnaryDelimiter.exec (equalValue a b)
  have hb:=Composition.executes equalUnaryMachine UnaryDelimiter.machine _ _ _ _ _
    (equalUnaryExec a b) hd
  have hc:=Composition.executes (FieldProjection.machine n keep)
    (Composition.machine equalUnaryMachine UnaryDelimiter.machine) _ _ _ _ _ hp hb
  have h:=RetainedInput.executes
    (Composition.machine (FieldProjection.machine n keep)
      (Composition.machine equalUnaryMachine UnaryDelimiter.machine)) _ _ _ hc
  rw [show (unary (equalValue a b)++[false])++stream xs=stream (equalValue a b::xs) by
    simp [stream,List.append_assoc]] at h
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hl:=fields_stream_length_le n keep 0 xs
  rw [hf] at hl
  have hs:(stream [a,b]).length=a+b+2 :=by simp [stream,unary_length];omega
  rw [hs] at hl
  have hr:equalValue a b≤1 :=by simp [equalValue,FlagUnary.value];split_ifs <;> omega
  simp only [equalityTime,FieldProjection.time,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,List.length_append,
    List.length_singleton,unary_length,pairInput_length]
  omega
namespace EightFlagOr
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 abbrev Label:=Fin 8×Bool×Bool×Bool
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 abbrev Statement:=TM2.Stmt (fun _:Fin 2=>Bool) Label (Option Bool)
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def left (k:Fin 8) (x z:Bool):Bool:=if k.val<4 then x&&z else x
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def right (k:Fin 8) (y z:Bool):Bool:=if k.val<4 then y else y&&z
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def program : Label→Statement
  | ⟨k,x,y,z⟩=>.pop 0 (fun _ h=>h) (.branch (fun v=>v.getD false)
      (.goto fun _=>⟨k,x,y,true⟩)
      (if h:k.val<7 then .goto fun _=>⟨⟨k.val+1,by omega⟩,left k x z,right k y z,false⟩
       else .push 1 (fun _=>left k x z || right k y z) (.load (fun _=>none) .halt)))
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def machine : Machine where
  K:=Fin 2;input:=0;output:=1;Λ:=Label;main:=⟨0,true,true,false⟩
  σ:=Option Bool;initial:=none;program:=program
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def cfg (k:Fin 8) (x y z:Bool) (s:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 2=>Bool) Label (Option Bool) :=⟨some ⟨k,x,y,z⟩,v,![s,[]]⟩
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem bit_step (k:Fin 8) (x y z:Bool) (s:List Bool) (v:Option Bool) :
    TM2.step program (cfg k x y z (true::s) v)=some (cfg k x y true s (some true)) :=by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext j;fin_cases j <;> simp [Function.update]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem sep_step (k:Fin 8) (hk:k.val<7) (x y z:Bool) (s:List Bool) (v:Option Bool) :
    TM2.step program (cfg k x y z (false::s) v)=
      some (cfg ⟨k.val+1,by omega⟩ (left k x z) (right k y z) false s (some false)) :=by
  simp [TM2.step,program,cfg,TM2.stepAux,hk,TM2.Cfg.mk.injEq]
  funext j;fin_cases j <;> simp [Function.update]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def halt (y:List Bool) : TM2.Cfg (fun _:Fin 2=>Bool) Label (Option Bool) :=⟨none,none,![[],y]⟩
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem halt_eq (y:List Bool) : halt y=machine.halt y :=by
  simp [halt,Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext j;fin_cases j <;> simp [Function.update]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem last_step (x y z:Bool) (v:Option Bool) :
    TM2.step program (cfg 7 x y z [] v)=some (halt [x || y&&z]) :=by
  simp [TM2.step,program,cfg,TM2.stepAux,left,right,halt,TM2.Cfg.mk.injEq]
  funext j;fin_cases j <;> simp [Function.update]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem field_run (k:Fin 8) (hk:k.val<7) (x y b:Bool) (s:List Bool) (v:Option Bool) :
    (fun c=>c.bind (TM2.step program))^[FlagUnary.value b+1]
      (some (cfg k x y false (unary (FlagUnary.value b)++false::s) v))=
      some (cfg ⟨k.val+1,by omega⟩ (left k x b) (right k y b) false s (some false)) :=by
  cases b <;> simp [FlagUnary.value,unary,Function.iterate_succ_apply,
    bit_step,sep_step k hk]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem last_run (x y b:Bool) (v:Option Bool) :
    (fun c=>c.bind (TM2.step program))^[FlagUnary.value b+1]
      (some (cfg 7 x y false (unary (FlagUnary.value b)) v))=
      some (halt [x || y&&b]) :=by
  cases b <;> simp [FlagUnary.value,unary,Function.iterate_succ_apply,bit_step,last_step]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem init_eq (w:List Bool) : machine.init w=cfg 0 true true false w none :=by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext j;fin_cases j <;> simp [Function.update]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def flags (a b c d e f g h:Bool):List ℕ :=
   [FlagUnary.value a,FlagUnary.value b,FlagUnary.value c,FlagUnary.value d,
    FlagUnary.value e,FlagUnary.value f,FlagUnary.value g,FlagUnary.value h]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem raw_flags (a b c d e f g h:Bool) : raw (flags a b c d e f g h)=
    unary (FlagUnary.value a)++false::(unary (FlagUnary.value b)++false::
      (unary (FlagUnary.value c)++false::(unary (FlagUnary.value d)++false::
       (unary (FlagUnary.value e)++false::(unary (FlagUnary.value f)++false::
        (unary (FlagUnary.value g)++false::unary (FlagUnary.value h))))))) :=by
  simpa [flags,stream,List.append_assoc] using
    raw_append_last [FlagUnary.value a,FlagUnary.value b,FlagUnary.value c,FlagUnary.value d,
      FlagUnary.value e,FlagUnary.value f,FlagUnary.value g] (FlagUnary.value h)
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem firstBlock_run (a b c d:Bool) (s:List Bool) (v:Option Bool) :
    (fun c=>c.bind (TM2.step program))^[(FlagUnary.value d+1)+(FlagUnary.value c+1)+
      (FlagUnary.value b+1)+(FlagUnary.value a+1)]
      (some (cfg 0 true true false (stream [FlagUnary.value a,FlagUnary.value b,
        FlagUnary.value c,FlagUnary.value d]++s) v))=
      some (cfg ⟨4,by decide⟩ (a&&b&&c&&d) true false s (some false)) :=by
  simp only [stream,List.append_assoc,List.cons_append,List.nil_append]
  rw [Function.iterate_add_apply,field_run 0 (by decide)]
  simp only [left,right,Fin.val_zero,Nat.reduceLT,↓reduceIte,Bool.true_and]
  rw [Function.iterate_add_apply,field_run _ (by decide)]
  simp only [left,right,Nat.reduceAdd,Nat.reduceLT,↓reduceIte]
  rw [Function.iterate_add_apply,field_run _ (by decide)]
  simp only [left,right,Nat.reduceAdd,Nat.reduceLT,↓reduceIte]
  rw [field_run _ (by decide)]
  simp only [left,right,Nat.reduceAdd,Nat.reduceLT,↓reduceIte,Bool.and_assoc]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem secondBlock_run (x e f g h:Bool) (v:Option Bool) :
    (fun c=>c.bind (TM2.step program))^[(FlagUnary.value h+1)+(FlagUnary.value g+1)+
      (FlagUnary.value f+1)+(FlagUnary.value e+1)]
      (some (cfg ⟨4,by decide⟩ x true false
        (raw [FlagUnary.value e,FlagUnary.value f,FlagUnary.value g,FlagUnary.value h]) v))=
      some (halt [x||(e&&f&&g&&h)]) :=by
  rw [raw_four]
  rw [Function.iterate_add_apply,field_run _ (by decide)]
  simp only [left,right,Nat.reduceAdd,Nat.reduceLT,↓reduceIte,Bool.true_and]
  rw [Function.iterate_add_apply,field_run _ (by decide)]
  simp only [left,right,Nat.reduceAdd,Nat.reduceLT,↓reduceIte]
  rw [Function.iterate_add_apply,field_run _ (by decide)]
  simp only [left,right,Nat.reduceAdd,Nat.reduceLT,↓reduceIte]
  change (fun c=>c.bind (TM2.step program))^[FlagUnary.value h+1]
    (some (cfg 7 x (e&&f&&g) false (unary (FlagUnary.value h)) (some false)))=_
  rw [last_run]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def exec (a b c d e f g h:Bool) : EvalsToInTime (TM2.step machine.program)
    (machine.init (raw (flags a b c d e f g h)))
    (some (machine.halt [(a&&b&&c&&d)||(e&&f&&g&&h)])) 16 :=by
  let s:=(FlagUnary.value h+1)+(FlagUnary.value g+1)+(FlagUnary.value f+1)+(FlagUnary.value e+1)+
    ((FlagUnary.value d+1)+(FlagUnary.value c+1)+(FlagUnary.value b+1)+(FlagUnary.value a+1))
  refine ⟨⟨s,?_⟩,?_⟩
  · rw [init_eq,←halt_eq]
    have hw:raw (flags a b c d e f g h)=
      stream [FlagUnary.value a,FlagUnary.value b,FlagUnary.value c,FlagUnary.value d]++
        raw [FlagUnary.value e,FlagUnary.value f,FlagUnary.value g,FlagUnary.value h] :=by
      rw [raw_flags,raw_four]
      simp only [stream,List.nil_append,List.append_assoc,List.cons_append]
    rw [hw]
    change (fun c:Option (TM2.Cfg (fun _:Fin 2=>Bool) Label (Option Bool))=>c.bind (TM2.step program))^[s]
      (some (cfg 0 true true false _ none))=some (halt [(a&&b&&c&&d)||(e&&f&&g&&h)])
    dsimp only [s]
    rw [Function.iterate_add_apply,firstBlock_run,secondBlock_run]
  · dsimp only [s]
    have hv (b:Bool):FlagUnary.value b≤1 :=by cases b <;> simp [FlagUnary.value]
    have:=hv a;have:=hv b;have:=hv c;have:=hv d;have:=hv e;have:=hv f;have:=hv g;have:=hv h
    omega
end EightFlagOr
end QEC.Coding.BitTuring.UnaryArithmetic.PSLComparisonSupport
