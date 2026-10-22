import QEC.Coding.BitTuring.UnaryPrefixProjection
import QEC.Coding.BitTuring.UnaryMatrixListQuery

/-!
# Actual finite unary ripple counter with retained trailing context

Fixed finite instructions parse a positive unary modulus and a fixed nonempty canonical
coordinate header. Each digit's comparison, equality carry, reset or increment is executed
on finite Boolean stacks. The same finite body handles every dynamic modulus, coordinate
and arbitrary Boolean suffix. Complete counted runs return the actual overflow flag and
advanced header, preserve suffix order, reset variables and clear all auxiliary tapes.
A faithful joint encoding and whole linear Mathlib certificate use no arithmetic/answer/
iteration/runtime callback inside instructions. The four-coordinate source SL counter and
original PSL list-position counter instantiate this body. Bool is the tape alphabet and
this internal proof closure does not prove the arbitrary-field public PK22 theorem.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
/-- Finite counter instructions/configurations and counted clean body execution. -/
abbrev Var (n:ℕ):=Fin (n+1)×Bool×Option Bool
/-- Finite counter instructions/configurations and counted clean body execution. -/
abbrev Statement (n:ℕ):=TM2.Stmt (fun _:Fin 8=>Bool) (Fin 12) (Var n)
/-- Finite counter instructions/configurations and counted clean body execution. -/
def nextIndex (n:ℕ) (k:Fin (n+1)):Fin (n+1):=if h:k.val<n then ⟨k.val+1,Nat.succ_lt_succ h⟩ else k
/-- Finite counter instructions/configurations and counted clean body execution. -/
def nextLabel (n:ℕ) (k:Fin (n+1)):Fin 12:=if k.val<n then 1 else 8
/-- Finite counter instructions/configurations and counted clean body execution. -/
def advance (n:ℕ):Statement n:=
 .branch (fun v=>decide (v.1.val<n))
  (.load (fun v=>(nextIndex n v.1,v.2.1,none)) (.goto fun _=>1))
  (.load (fun v=>(v.1,v.2.1,none)) (.goto fun _=>8))
/-- Finite counter instructions/configurations and counted clean body execution. -/
def setHead {n:ℕ} (v:Var n) (h:Option Bool):Var n:=(v.1,v.2.1,h)
/-- Finite counter instructions/configurations and counted clean body execution. -/
def program (n:ℕ):Fin 12→Statement n
 | 0 =>.pop 0 setHead (.branch (fun v=>v.2.2.getD false)
     (.push 1 (fun _=>true) (.push 5 (fun _=>true) (.goto fun _=>0)))
     (.push 5 (fun _=>false) (.load (fun _=>(0,true,none)) (.goto fun _=>1))))
 | 1 =>.pop 1 setHead (.branch (fun v=>v.2.2.isSome)
     (.push 2 (fun v=>v.2.2.getD false) (.push 7 (fun v=>v.2.2.getD false) (.goto fun _=>1)))
     (.goto fun _=>2))
 | 2 =>.pop 7 setHead (.branch (fun v=>v.2.2.isSome)
     (.push 1 (fun v=>v.2.2.getD false) (.goto fun _=>2))
     (.branch (fun v=>v.2.1)
       (.push 3 (fun _=>true) (.push 4 (fun _=>true) (.goto fun _=>3)))
       (.goto fun _=>3)))
 | 3 =>.pop 0 setHead (.branch (fun v=>v.2.2.getD false)
     (.push 3 (fun _=>true) (.push 4 (fun _=>true) (.goto fun _=>3)))
     (.goto fun _=>4))
 | 4 =>.pop 4 setHead (.branch (fun v=>v.2.2.isSome)
     (.pop 2 setHead (.goto fun _=>4))
     (.pop 2 setHead (.load (fun v=>(v.1,!v.2.2.isSome,v.2.2)) (.goto fun _=>5))))
 | 5 =>.pop 2 setHead (.branch (fun v=>v.2.2.isSome)
     (.goto fun _=>5) (.goto fun v=>if v.2.1 then 6 else 7))
 | 6 =>.pop 3 setHead (.branch (fun v=>v.2.2.isSome)
     (.goto fun _=>6) (.push 5 (fun _=>false) (advance n)))
 | 7 =>.pop 3 setHead (.branch (fun v=>v.2.2.isSome)
     (.push 5 (fun v=>v.2.2.getD false) (.goto fun _=>7))
     (.push 5 (fun _=>false) (advance n)))
 | 8 =>.pop 1 setHead (.branch (fun v=>v.2.2.isSome) (.goto fun _=>8) (.goto fun _=>9))
 | 9 =>.pop 0 setHead (.branch (fun v=>v.2.2.isSome)
     (.push 5 (fun v=>v.2.2.getD false) (.goto fun _=>9)) (.goto fun _=>10))
 | 10 =>.pop 5 setHead (.branch (fun v=>v.2.2.isSome)
     (.push 6 (fun v=>v.2.2.getD false) (.goto fun _=>10)) (.goto fun _=>11))
 | _ =>.push 6 (fun v=>v.2.1) (.load (fun _=>(0,true,none)) .halt)
/-- Finite counter instructions/configurations and counted clean body execution. -/
def machine (n:ℕ):Machine where
 K:=Fin 8;input:=0;output:=6;Λ:=Fin 12;main:=0;σ:=Var n;initial:=(0,true,none);program:=program n
/-- Finite counter instructions/configurations and counted clean body execution. -/
def cfg (n:ℕ) (phase:Fin 12) (k:Fin (n+1)) (carry:Bool) (v:Option Bool)
 (S Q L C M B D T:List Bool):TM2.Cfg (fun _:Fin 8=>Bool) (Fin 12) (Var n):=
 ⟨some phase,(k,carry,v),![S,Q,L,C,M,B,D,T]⟩
/-- Finite counter instructions/configurations and counted clean body execution. -/
def nextCfg (n:ℕ) (k:Fin (n+1)) (carry:Bool) (S Q B:List Bool):=
 cfg n (nextLabel n k) (nextIndex n k) carry none S Q [] [] [] B [] []
-- Actual q parsing preserves its independent copy and reversed output header.
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem q_cons (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q B:List Bool):
 TM2.step (program n) (cfg n 0 k carry v (true::s) Q [] [] [] B [] [])=
 some (cfg n 0 k carry (some true) s (true::Q) [] [] [] (true::B) [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem q_sep (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q B:List Bool):
 TM2.step (program n) (cfg n 0 k carry v (false::s) Q [] [] [] B [] [])=
 some (cfg n 1 0 true none s Q [] [] [] (false::B) [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem q_run (n q:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q B:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[q+1]
  (some (cfg n 0 k carry v (unary q++false::s) Q [] [] [] B [] []))=
 some (cfg n 1 0 true none s (unary q++Q) [] [] [] (false::(unary q++B)) [] []):=by
 induction q generalizing Q B v with
 |zero=>simp [q_sep]
 |succ q ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,q_cons]
  simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (some true) (true::Q) (true::B)
-- One actual q-copy pass and its restore pass prepare a candidate increment.
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem copyq_cons (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (a:Bool) (s Q L B T:List Bool):
 TM2.step (program n) (cfg n 1 k carry v s (a::Q) L [] [] B [] T)=
 some (cfg n 1 k carry (some a) s Q (a::L) [] [] B [] (a::T)):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem copyq_nil (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s L B T:List Bool):
 TM2.step (program n) (cfg n 1 k carry v s [] L [] [] B [] T)=
 some (cfg n 2 k carry none s [] L [] [] B [] T):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem copyq_run (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q L B T:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[Q.length+1]
  (some (cfg n 1 k carry v s Q L [] [] B [] T))=
 some (cfg n 2 k carry none s [] (Q.reverse++L) [] [] B [] (Q.reverse++T)):=by
 induction Q generalizing L T v with
 |nil=>simpa using copyq_nil n k carry v s L B T
 |cons a Q ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,copyq_cons]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- Finite counter instructions/configurations and counted clean body execution. -/
def bump (carry:Bool):ℕ:=if carry then 1 else 0
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem restore_cons (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (a:Bool) (s Q L B T:List Bool):
 TM2.step (program n) (cfg n 2 k carry v s Q L [] [] B [] (a::T))=
 some (cfg n 2 k carry (some a) s (a::Q) L [] [] B [] T):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem restore_nil (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q L B:List Bool):
 TM2.step (program n) (cfg n 2 k carry v s Q L [] [] B [] [])=
 some (cfg n 3 k carry none s Q L (unary (bump carry)) (unary (bump carry)) B [] []):=by
 cases carry <;> simp [TM2.step,program,cfg,setHead,bump,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem restore_run (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q L B T:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[T.length+1]
  (some (cfg n 2 k carry v s Q L [] [] B [] T))=
 some (cfg n 3 k carry none s (T.reverse++Q) L (unary (bump carry)) (unary (bump carry)) B [] []):=by
 induction T generalizing Q v with
 |nil=>simpa using restore_nil n k carry v s Q L B
 |cons a T ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,restore_cons]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
-- Actual field parsing duplicates the candidate for comparison and possible emission.
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem digit_cons (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q L C M B:List Bool):
 TM2.step (program n) (cfg n 3 k carry v (true::s) Q L C M B [] [])=
 some (cfg n 3 k carry (some true) s Q L (true::C) (true::M) B [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem digit_sep (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q L C M B:List Bool):
 TM2.step (program n) (cfg n 3 k carry v (false::s) Q L C M B [] [])=
 some (cfg n 4 k carry (some false) s Q L C M B [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem digit_run (n x:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q L C M B:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[x+1]
  (some (cfg n 3 k carry v (unary x++false::s) Q L C M B [] []))=
 some (cfg n 4 k carry (some false) s Q L (unary x++C) (unary x++M) B [] []):=by
 induction x generalizing C M v with
 |zero=>simp [digit_sep]
 |succ x ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,digit_cons]
  simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (some true) (true::C) (true::M)

-- Actual cancellation derives the carry; no arithmetic comparison is in an instruction.
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem match_both (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (a b:Bool) (s Q L C M B:List Bool):
 TM2.step (program n) (cfg n 4 k carry v s Q (a::L) C (b::M) B [] [])=
 some (cfg n 4 k carry (some a) s Q L C M B [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem match_equal_end (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q C B:List Bool):
 TM2.step (program n) (cfg n 4 k carry v s Q [] C [] B [] [])=
 some (cfg n 5 k true none s Q [] C [] B [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem match_less_end (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (a:Bool) (s Q L C B:List Bool):
 TM2.step (program n) (cfg n 4 k carry v s Q (a::L) C [] B [] [])=
 some (cfg n 5 k false (some a) s Q L C [] B [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem match_equal_run (n y:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q C B:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[y+1]
  (some (cfg n 4 k carry v s Q (unary y) C (unary y) B [] []))=
 some (cfg n 5 k true none s Q [] C [] B [] []):=by
 induction y generalizing v with
 |zero=>simp [match_equal_end]
 |succ y ih=>
  simp only [unary_succ]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,match_both]
  exact ih (some true)
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem match_less_run (n y r:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q C B:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[y+1]
  (some (cfg n 4 k carry v s Q (unary (y+r+1)) C (unary y) B [] []))=
 some (cfg n 5 k false (some true) s Q (unary r) C [] B [] []):=by
 induction y generalizing v with
 |zero=>simp [unary_succ,match_less_end]
 |succ y ih=>
  rw [show y+1+r+1=(y+r+1)+1 by omega]
  simp only [unary_succ]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,match_both]
  exact ih (some true)
/-- Finite counter instructions/configurations and counted clean body execution. -/
def candidatePhase (carry:Bool):Fin 12:=if carry then 6 else 7
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem limit_cons (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (a:Bool) (s Q L C B:List Bool):
 TM2.step (program n) (cfg n 5 k carry v s Q (a::L) C [] B [] [])=
 some (cfg n 5 k carry (some a) s Q L C [] B [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem limit_nil (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q C B:List Bool):
 TM2.step (program n) (cfg n 5 k carry v s Q [] C [] B [] [])=
 some (cfg n (candidatePhase carry) k carry none s Q [] C [] B [] []):=by
 cases carry <;> simp [TM2.step,program,cfg,setHead,candidatePhase,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem limit_run (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q L C B:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[L.length+1]
  (some (cfg n 5 k carry v s Q L C [] B [] []))=
 some (cfg n (candidatePhase carry) k carry none s Q [] C [] B [] []):=by
 induction L generalizing v with
 |nil=>simpa using limit_nil n k carry v s Q C B
 |cons a L ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,limit_cons]
  exact ih (some a)
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem candidate_cons (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (a:Bool) (s Q C B:List Bool):
 TM2.step (program n) (cfg n (candidatePhase carry) k carry v s Q [] (a::C) [] B [] [])=
 some (cfg n (candidatePhase carry) k carry (some a) s Q [] C [] (if carry then B else a::B) [] []):=by
 cases carry <;> simp [TM2.step,program,cfg,setHead,candidatePhase,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
  (funext j;fin_cases j <;> simp [Function.update])
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem candidate_nil (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q B:List Bool):
 TM2.step (program n) (cfg n (candidatePhase carry) k carry v s Q [] [] [] B [] [])=
 some (nextCfg n k carry s Q (false::B)):=by
 cases carry <;> by_cases hk:k.val<n <;>
  simp [TM2.step,program,cfg,setHead,candidatePhase,advance,nextCfg,nextIndex,nextLabel,hk,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
  (funext j;fin_cases j <;> simp [Function.update])
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem candidate_run (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q C B:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[C.length+1]
  (some (cfg n (candidatePhase carry) k carry v s Q [] C [] B [] []))=
 some (nextCfg n k carry s Q (false::(if carry then B else C.reverse++B))):=by
 induction C generalizing B v with
 |nil=>simpa using candidate_nil n k carry v s Q B
 |cons a C ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,candidate_cons]
  rw [ih]
  cases carry <;> simp only [Bool.false_eq_true,↓reduceIte,List.reverse_cons,List.append_assoc,List.singleton_append]
-- Semantic specifications of one digit and exact instruction counts.
/-- Finite counter instructions/configurations and counted clean body execution. -/
def candidate (x:ℕ) (carry:Bool):ℕ:=x+bump carry
/-- Finite counter instructions/configurations and counted clean body execution. -/
def carried (q x:ℕ) (carry:Bool):Bool:=decide (candidate x carry=q)
/-- Finite counter instructions/configurations and counted clean body execution. -/
def digit (q x:ℕ) (carry:Bool):ℕ:=if carried q x carry then 0 else candidate x carry
/-- Finite counter instructions/configurations and counted clean body execution. -/
def fieldSteps (q x:ℕ) (carry:Bool):ℕ:=
 2*(q+1)+(x+1)+(candidate x carry+1)+(q-candidate x carry-1+1)+(candidate x carry+1)
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem candidate_le (q x:ℕ) (carry:Bool) (hx:x<q):candidate x carry≤q:=by
 cases carry <;> simp [candidate,bump] <;> omega
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem fieldSteps_le (q x:ℕ) (carry:Bool) (hx:x<q):fieldSteps q x carry≤6*(q+1):=by
 have hy:=candidate_le q x carry hx
 simp only [fieldSteps]
 omega
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem one_run (n q x:ℕ) (k:Fin (n+1)) (carry:Bool) (s B:List Bool) (hx:x<q):
 (fun c=>c.bind (TM2.step (program n)))^[fieldSteps q x carry]
  (some (cfg n 1 k carry none (unary x++false::s) (unary q) [] [] [] B [] []))=
 some (nextCfg n k (carried q x carry) s (unary q) (false::(unary (digit q x carry)++B))):=by
 let y:=candidate x carry
 have hy:y≤q:=candidate_le q x carry hx
 have he:unary x++unary (bump carry)=unary y:=by rw [←unary_add];rfl
 have hcopy:=copyq_run n k carry none (unary x++false::s) (unary q) [] B []
 simp only [unary_length,show (unary q).reverse=unary q by simp [unary],List.append_nil] at hcopy
 have hrestore:=restore_run n k carry none (unary x++false::s) [] (unary q) B (unary q)
 simp only [unary_length,show (unary q).reverse=unary q by simp [unary],List.append_nil] at hrestore
 have hprep:(fun c=>c.bind (TM2.step (program n)))^[(x+1)+(q+1)+(q+1)]
  (some (cfg n 1 k carry none (unary x++false::s) (unary q) [] [] [] B [] []))=
  some (cfg n 4 k carry (some false) s (unary q) (unary q) (unary y) (unary y) B [] []):=by
  rw [Function.iterate_add_apply,hcopy,Function.iterate_add_apply,hrestore,digit_run,he]

 by_cases hq:y=q
 · rw [hq] at hprep
   have hcy:carried q x carry=true:=by simp [carried,show candidate x carry=q from hq]
   have hdi:digit q x carry=0:=by simp [digit,hcy]
   rw [hcy,hdi]
   have hs:fieldSteps q x carry=(q+1)+1+(q+1)+((x+1)+(q+1)+(q+1)):=by
    simp only [fieldSteps,show candidate x carry=q from hq];omega
   rw [hs,Function.iterate_add_apply,hprep,Function.iterate_add_apply,match_equal_run,
    Function.iterate_add_apply]
   have hl:=limit_run n k true none s (unary q) [] (unary q) B
   simp only [List.length_nil,Nat.zero_add] at hl
   have hc:=candidate_run n k true none s (unary q) (unary q) B
   simp only [unary_length,↓reduceIte] at hc
   rw [hl,hc]
   simp only [unary_zero,List.nil_append]

 · have hlt:y<q:=by omega
   let r:=q-y-1
   have hqr:q=y+r+1:=by dsimp [r];omega
   have hcy:carried q x carry=false:=by simp [carried,show candidate x carry≠q from hq]
   have hdi:digit q x carry=y:=by simp only [digit,hcy,Bool.false_eq_true,↓reduceIte];rfl
   rw [hcy,hdi]
   have hs:fieldSteps q x carry=(y+1)+(r+1)+(y+1)+((x+1)+(q+1)+(q+1)):=by
    simp only [fieldSteps];dsimp [r,y];omega
   rw [hs,Function.iterate_add_apply,hprep,Function.iterate_add_apply]
   have hm:=match_less_run n y r k carry (some false) s (unary q) (unary y) B
   rw [←hqr] at hm
   rw [hm,Function.iterate_add_apply]
   have hl:=limit_run n k false (some true) s (unary q) (unary r) (unary y) B
   simp only [unary_length] at hl
   have hc:=candidate_run n k false none s (unary q) (unary y) B
   simp only [unary_length,show (unary y).reverse=unary y by simp [unary],Bool.false_eq_true,↓reduceIte] at hc
   rw [hl,hc]


-- Mathematical ripple result and exact component-derived time, never callbacks.
/-- Finite counter instructions/configurations and counted clean body execution. -/
def digits (q:ℕ):Bool→List ℕ→Bool×List ℕ
 | carry,[] =>(carry,[])
 | carry,x::xs =>let r:=digits q (carried q x carry) xs;(r.1,digit q x carry::r.2)
/-- Finite counter instructions/configurations and counted clean body execution. -/
def coordsSteps (q:ℕ):Bool→List ℕ→ℕ
 | _,[]=>0
 | carry,x::xs=>coordsSteps q (carried q x carry) xs+fieldSteps q x carry
/-- Finite counter instructions/configurations and counted clean body execution. -/
def lastIndex (n:ℕ):Fin (n+1):=⟨n,by omega⟩
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem digits_length (q:ℕ) (carry:Bool) (xs:List ℕ):(digits q carry xs).2.length=xs.length:=by
 induction xs generalizing carry with
 |nil=>rfl
 |cons x xs ih=>simp only [digits,List.length_cons,ih]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem digit_lt (q x:ℕ) (carry:Bool) (hx:x<q):digit q x carry<q:=by
 have hy:=candidate_le q x carry hx
 unfold digit carried
 split_ifs with he
 · omega
 · have hn:candidate x carry≠q:=by simpa only [decide_eq_true_eq] using he
   omega
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem digits_lt (q:ℕ) (carry:Bool) (xs:List ℕ) (hx:∀x∈xs,x<q):
 ∀x∈(digits q carry xs).2,x<q:=by
 induction xs generalizing carry with
 |nil=>simp [digits]
 |cons x xs ih=>
  have h0:=digit_lt q x carry (hx x (by simp))
  have ht:=ih (carried q x carry) (fun z hz=>hx z (by simp [hz]))
  simpa only [digits,List.mem_cons,forall_eq_or_imp] using And.intro h0 ht
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem coordsSteps_le (q:ℕ) (carry:Bool) (xs:List ℕ) (hx:∀x∈xs,x<q):
 coordsSteps q carry xs≤xs.length*(6*(q+1)):=by
 induction xs generalizing carry with
 |nil=>simp [coordsSteps]
 |cons x xs ih=>
  have h0:=fieldSteps_le q x carry (hx x (by simp))
  have ht:=ih (carried q x carry) (fun z hz=>hx z (by simp [hz]))
  simp only [coordsSteps,List.length_cons,Nat.add_mul,Nat.one_mul]
  omega
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem fields_run (n q:ℕ) (xs:List ℕ) (k:Fin (n+1)) (carry:Bool) (s B:List Bool)
 (hk:k.val+xs.length=n+1) (hx:∀x∈xs,x<q):
 (fun c=>c.bind (TM2.step (program n)))^[coordsSteps q carry xs]
  (some (cfg n 1 k carry none (stream xs++s) (unary q) [] [] [] B [] []))=
 some (cfg n 8 (lastIndex n) (digits q carry xs).1 none s (unary q) [] [] []
  ((stream (digits q carry xs).2).reverse++B) [] []):=by
 induction xs generalizing k carry B with
 |nil=>have hlt:=k.isLt;simp only [List.length_nil] at hk;omega
 |cons x xs ih=>
  have h0:=hx x (by simp)
  have ht:∀z∈xs,z<q:=fun z hz=>hx z (by simp [hz])
  have he:stream (x::xs)++s=unary x++false::(stream xs++s):=by
   simp only [stream,List.cons_append,List.append_assoc]
  cases xs with
  |nil=>
   have hkl:k.val=n:=by simp only [List.length_cons,List.length_nil] at hk;omega
   have hkn:k=lastIndex n:=Fin.ext hkl
   subst k
   have h:=one_run n q x (lastIndex n) carry s B h0
   simpa only [coordsSteps,Nat.zero_add,digits,stream,List.nil_append,List.append_nil,nextCfg,nextIndex,
    nextLabel,lastIndex,show ¬n<n from lt_irrefl n,↓reduceDIte,↓reduceIte,List.reverse_append,List.reverse_cons,
    List.reverse_nil,unary,List.reverse_replicate,List.append_assoc,List.singleton_append,List.cons_append] using h
  |cons y ys=>
   have hkl:k.val<n:=by simp only [List.length_cons] at hk;omega
   have hk':(nextIndex n k).val+(y::ys).length=n+1:=by
    simp only [nextIndex,hkl,↓reduceDIte,List.length_cons] at *;omega
   rw [coordsSteps,Function.iterate_add_apply,he,one_run n q x k carry (stream (y::ys)++s) B h0]
   simp only [nextCfg,nextLabel,hkl,↓reduceIte]
   have h:=ih (nextIndex n k) (carried q x carry) (false::(unary (digit q x carry)++B)) hk' ht
   rw [h]
   simp only [digits,stream,List.reverse_append,List.reverse_cons,
    unary,List.reverse_replicate,List.append_assoc,List.cons_append]
   rfl
-- Complete actual modulus cleanup, arbitrary tail copying, reversal and flag emission.
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem cleanup_cons (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (a:Bool) (s Q B:List Bool):
 TM2.step (program n) (cfg n 8 k carry v s (a::Q) [] [] [] B [] [])=
 some (cfg n 8 k carry (some a) s Q [] [] [] B [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem cleanup_nil (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s B:List Bool):
 TM2.step (program n) (cfg n 8 k carry v s [] [] [] [] B [] [])=
 some (cfg n 9 k carry none s [] [] [] [] B [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem cleanup_run (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s Q B:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[Q.length+1]
  (some (cfg n 8 k carry v s Q [] [] [] B [] []))=
 some (cfg n 9 k carry none s [] [] [] [] B [] []):=by
 induction Q generalizing v with
 |nil=>simpa using cleanup_nil n k carry v s B
 |cons a Q ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,cleanup_cons]
  exact ih (some a)
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem tail_cons (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (a:Bool) (s B:List Bool):
 TM2.step (program n) (cfg n 9 k carry v (a::s) [] [] [] [] B [] [])=
 some (cfg n 9 k carry (some a) s [] [] [] [] (a::B) [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem tail_nil (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (B:List Bool):
 TM2.step (program n) (cfg n 9 k carry v [] [] [] [] [] B [] [])=
 some (cfg n 10 k carry none [] [] [] [] [] B [] []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem tail_run (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (s B:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[s.length+1]
  (some (cfg n 9 k carry v s [] [] [] [] B [] []))=
 some (cfg n 10 k carry none [] [] [] [] [] (s.reverse++B) [] []):=by
 induction s generalizing B v with
 |nil=>simpa using tail_nil n k carry v B
 |cons a s ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,tail_cons]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem reverse_cons (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (a:Bool) (B D:List Bool):
 TM2.step (program n) (cfg n 10 k carry v [] [] [] [] [] (a::B) D [])=
 some (cfg n 10 k carry (some a) [] [] [] [] [] B (a::D) []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem reverse_nil (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (D:List Bool):
 TM2.step (program n) (cfg n 10 k carry v [] [] [] [] [] [] D [])=
 some (cfg n 11 k carry none [] [] [] [] [] [] D []):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem reverse_run (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (B D:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[B.length+1]
  (some (cfg n 10 k carry v [] [] [] [] [] B D []))=
 some (cfg n 11 k carry none [] [] [] [] [] [] (B.reverse++D) []):=by
 induction B generalizing D v with
 |nil=>simpa using reverse_nil n k carry v D
 |cons a B ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,reverse_cons]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem emit (n:ℕ) (k:Fin (n+1)) (carry:Bool) (v:Option Bool) (D:List Bool):
 TM2.step (program n) (cfg n 11 k carry v [] [] [] [] [] [] D [])=
 some ((machine n).halt (carry::D)):=by
 simp [TM2.step,program,cfg,Machine.halt,machine,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem finish_run (n:ℕ) (k:Fin (n+1)) (carry:Bool) (s Q B:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[Q.length+B.length+2*s.length+4]
  (some (cfg n 8 k carry none s Q [] [] [] B [] []))=
 some ((machine n).halt (carry::(B.reverse++s))):=by
 rw [show Q.length+B.length+2*s.length+4=
   1+((s.reverse++B).length+1)+(s.length+1)+(Q.length+1) by simp only [List.length_append,List.length_reverse];omega,
   Function.iterate_add_apply,cleanup_run,Function.iterate_add_apply,tail_run,
   Function.iterate_add_apply,reverse_run]
 simp only [List.append_nil,Function.iterate_one,Option.bind_some,emit,List.reverse_append,List.reverse_reverse]
 rfl

/-- Finite counter instructions/configurations and counted clean body execution. -/
def output (q:ℕ) (xs:List ℕ) (s:List Bool):List Bool:=
 (digits q true xs).1::(stream (q::(digits q true xs).2)++s)
/-- Finite counter instructions/configurations and counted clean body execution. -/
def steps (q:ℕ) (xs:List ℕ) (s:List Bool):ℕ:=
 (q+(stream (q::(digits q true xs).2)).length+2*s.length+4)+coordsSteps q true xs+(q+1)
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem init_eq (n:ℕ) (w:List Bool):(machine n).init w=cfg n 0 0 true none w [] [] [] [] [] [] []:=by
 simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem run (n q:ℕ) (xs:List ℕ) (s:List Bool) (hlen:xs.length=n+1) (hx:∀x∈xs,x<q):
 (fun c=>c.bind (TM2.step (machine n).program))^[steps q xs s]
  (some ((machine n).init (stream (q::xs)++s)))=
 some ((machine n).halt (output q xs s)):=by
 let ys:=(digits q true xs).2
 let B:=(stream ys).reverse++false::unary q
 have hB:B.reverse=stream (q::ys):=by
  simp only [B,stream,List.reverse_append,List.reverse_cons,List.reverse_reverse,
   show (unary q).reverse=unary q by simp [unary],List.append_assoc,List.singleton_append]
 have hBL:B.length=(stream (q::ys)).length:=by
  simpa only [List.length_reverse] using congrArg List.length hB
 have he:stream (q::xs)++s=unary q++false::(stream xs++s):=by
  simp only [stream,List.cons_append,List.append_assoc]
 rw [init_eq,he]
 change (fun c=>c.bind (TM2.step (program n)))^[steps q xs s]
  (some (cfg n 0 0 true none (unary q++false::(stream xs++s)) [] [] [] [] [] [] []))=_
 rw [steps,Function.iterate_add_apply,q_run]
 simp only [List.append_nil]
 rw [Function.iterate_add_apply,fields_run n q xs 0 true s (false::unary q) (by simpa using hlen) hx]
 have hf:=finish_run n (lastIndex n) (digits q true xs).1 s (unary q) B
 rw [unary_length,hBL,hB] at hf
 exact hf
/-- Finite counter instructions/configurations and counted clean body execution. -/
def exec (n q:ℕ) (xs:List ℕ) (s:List Bool) (hlen:xs.length=n+1) (hx:∀x∈xs,x<q):
 EvalsToInTime (TM2.step (machine n).program) ((machine n).init (stream (q::xs)++s))
  (some ((machine n).halt (output q xs s))) (steps q xs s):=
 ⟨⟨steps q xs s,run n q xs s hlen hx⟩,le_refl _⟩
/-- Finite counter instructions/configurations and counted clean body execution. -/
noncomputable def time (n:ℕ):Polynomial ℕ:=Polynomial.C (8*(n+2)+8)*(Polynomial.X+1)
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem output_header_length_le (n q:ℕ) (xs:List ℕ) (hlen:xs.length=n+1) (hx:∀x∈xs,x<q):
 (stream (q::(digits q true xs).2)).length≤(n+2)*(q+1):=by
 have hb:=MatrixListQuery.stream_length_bound q (digits q true xs).2 (digits_lt q true xs hx)
 rw [digits_length,hlen] at hb
 simp only [stream,List.length_append,List.length_cons,unary_length]
 nlinarith
/-- Finite counter instructions/configurations and counted clean body execution. -/
noncomputable def polyExec (n q:ℕ) (xs:List ℕ) (s:List Bool) (hlen:xs.length=n+1) (hx:∀x∈xs,x<q):
 EvalsToInTime (TM2.step (machine n).program) ((machine n).init (stream (q::xs)++s))
  (some ((machine n).halt (output q xs s))) ((time n).eval (stream (q::xs)++s).length):=by
 have h:=exec n q xs s hlen hx
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 let L:=(stream (q::xs)++s).length
 have hq:q+1≤L+1:=by dsimp [L];simp only [stream,List.length_append,List.length_cons,unary_length];omega
 have hs:s.length≤L:=by dsimp [L];simp only [List.length_append];omega
 have hc:coordsSteps q true xs≤(n+1)*6*(L+1):=by
  have hb:=coordsSteps_le q true xs hx
  rw [hlen] at hb
  have hmul:=Nat.mul_le_mul_left ((n+1)*6) hq
  nlinarith
 have ho:(stream (q::(digits q true xs).2)).length≤(n+2)*(L+1):=
  (output_header_length_le n q xs hlen hx).trans (Nat.mul_le_mul_left (n+2) hq)
 change steps q xs s≤(time n).eval L
 simp only [steps,time,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
 nlinarith
-- The faithful domain contains only genuine modulus/coordinates/arity constraints and a suffix.
/-- Finite counter instructions/configurations and counted clean body execution. -/
def Input (n:ℕ):Type:= {z:ℕ×List ℕ//0<z.1 ∧ z.2.length=n+1 ∧ ∀x∈z.2,x<z.1}×List Bool
/-- Finite counter instructions/configurations and counted clean body execution. -/
def input (n:ℕ) (x:Input n):List Bool:=stream (x.1.val.1::x.1.val.2)++x.2
/-- Finite counter instructions/configurations and counted clean body execution. -/
theorem input_injective (n:ℕ):Function.Injective (input n):=by
 intro x y h
 have he:=PrefixProjection.stream_suffix_injective (x.1.val.1::x.1.val.2) (y.1.val.1::y.1.val.2) x.2 y.2
  (by simp only [List.length_cons];rw [x.1.property.2.1,y.1.property.2.1]) h
 have hh:=List.cons.inj he.1
 exact Prod.ext (Subtype.ext (Prod.ext hh.1 hh.2)) he.2
/-- Finite counter instructions/configurations and counted clean body execution. -/
noncomputable def computableInPolyTime (n:ℕ):
 TM2ComputableInPolyTime (input n) id (fun x:Input n=>output x.1.val.1 x.1.val.2 x.2) where
 tm:=(machine n).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time n
 outputsFun:=fun x=>by
  change TM2OutputsInTime (machine n).toFinTM2 (List.map id (input n x))
   (some (List.map id (output x.1.val.1 x.1.val.2 x.2))) ((time n).eval (input n x).length)
  have h:=Machine.outputsInTime (machine n) _ _ _
   (polyExec n x.1.val.1 x.1.val.2 x.2 x.1.property.2.1 x.1.property.2.2)
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [input,List.map_id] using h

end QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
