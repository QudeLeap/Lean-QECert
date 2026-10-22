import QEC.Coding.BitTuring.UnaryFourFieldRowsFilter
import QEC.Coding.ExpanderCodes.LPSPSLSearchMachine
import QEC.Coding.ExpanderCodes.LPSOriginalSLListMachine

/-!
# Complete actual original ordered PSL-list program

A fixed finite program reads only unary prime q. Actual merged SL enumeration, prefix branching, delimiter, reversal and input retention initialize the original forward rows. The concrete later-row search controls collection. Remaining-row induction and the combined source/accepted-buffer size invariant prove actual termination, complete cleanup and polynomial time. Raw output encodes exactly the original LAST-occurrence representatives, whose mapped quotient list equals lpsPSLList. Faithful unary input, standard Mathlib certificates and the genuine residue-prime PSL carrier budget follow. Original PSL index/lookup, full sparse CSS execution and unconditional strong centered-theta growth remain obligations; the public arbitrary-field/every-rate/cofinal/uniform-locality/two-sided-distance PK22 theorem remains unproved.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def search:=retainedSearchMachine
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def machine:=QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.machine search
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def state (q:ℕ) (R:List SL(2,ZMod q)) (C:List Bool):=
 cfg search 0 false none (qword q++rows q R) [] [] C []
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem search_io:search.input≠search.output:=by simp [search,retainedSearchMachine,RetainedInput.machine]
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem input_eq (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 input q A R=qword q++rows q (A::R):=by
 simp [QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.input,header,rows_cons,stream,qword,List.append_assoc]
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def invocationExec (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q))
 (R:List SL(2,ZMod q)) (C:List Bool):
 EvalsToInTime (TM2.step machine.program) (state q (A::R) C)
  (some (state q R (pushed (found q A R) (stream (coords q A)) C)))
  (retainedSearchTime.eval (input q A R).length+4*(q+1)+(stream (coords q A)).length+2*(rows q R).length+6):=by
 let hQ:=retainedSearchExec q A R
 have hin:=input_eq q A R
 have hentry:=entry_run search search_io q (rows q (A::R)) C (by intro he;have hh:=rows_cons_nonempty q A R;simp [he] at hh)
 have hbody:=body_run search C (input q A R) (found q A R::input q A R) hQ.steps hQ.evals_in_steps
 have hparse:=parse_current_run search search_io (found q A R) q (coords q A)
  (by simp [coords,LPSMatrixProductMachine.fields]) (rows q R) C
 have hafter:=after_run search search_io (found q A R) (some false) q (rows q R)
  (pushed (found q A R) (stream (coords q A)) C)
 have hRun:(next search)^[
  (2*(rows q R).length+(q+1)+3)+((stream (coords q A)).length+(q+1)+1)+hQ.steps+(2*(q+1)+2)]
  (some (state q (A::R) C))=some (state q R (pushed (found q A R) (stream (coords q A)) C)):=by
  unfold state
  rw [Function.iterate_add_apply,hentry,Function.iterate_add_apply]
  simp only [hin] at hbody
  rw [hbody,embed_halt search search_io,Function.iterate_add_apply]
  simp only [rows_cons,←List.append_assoc]
  rw [hparse,hafter]
 refine ⟨⟨_,hRun⟩,?_⟩
 have hm:=hQ.steps_le_m
 change (2*(rows q R).length+(q+1)+3)+((stream (coords q A)).length+(q+1)+1)+hQ.steps+(2*(q+1)+2)≤_
 omega
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def collected (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)) (C:List Bool):List Bool:=
 (rows q (representatives q R)).reverse++C
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def stateSize (q:ℕ) (R:List SL(2,ZMod q)) (C:List Bool):ℕ:=(qword q++rows q R).length+C.length
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem pushed_length (f:Bool) (w C:List Bool):(pushed f w C).length≤w.length+C.length:=by
 cases f <;>simp [pushed]
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem stateSize_cons (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)) (C:List Bool):
 stateSize q (A::R) C=(q+1)+(stream (coords q A)).length+(rows q R).length+C.length:=by
 simp only [stateSize,rows_cons,List.length_append,qword_length,Nat.add_assoc]
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem stateSize_next (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)) (C:List Bool):
 stateSize q R (pushed (found q A R) (stream (coords q A)) C)≤ stateSize q (A::R) C:=by
 have hc:=pushed_length (found q A R) (stream (coords q A)) C
 rw [stateSize_cons]
 simp only [stateSize,List.length_append,qword_length]
 omega
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem collected_cons (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)) (C:List Bool):
 collected q (A::R) C=collected q R (pushed (found q A R) (stream (coords q A)) C):=by
 cases hf:found q A R <;>simp [collected,representatives,hf,pushed,rows_cons,List.reverse_append,List.append_assoc]
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def callBudget (L:ℕ):ℕ:=retainedSearchTime.eval L+10*L+10
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def executeAux (q L:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)) (C:List Bool)
 (hsize:stateSize q R C≤ L):
 EvalsToInTime (TM2.step machine.program) (state q R C)
  (some (machine.halt (collected q R C).tail.reverse)) ((R.length+1)*callBudget L):=by
 induction R generalizing C with
 |nil=>
  have hr:=empty_run search search_io q C
  have hh:EvalsToInTime (TM2.step machine.program) (state q [] C)
   (some (machine.halt (collected q [] C).tail.reverse)) (2*(q+1)+C.tail.length+4):=by
   refine ⟨⟨_,?_⟩,le_refl _⟩
   simp only [state,collected,representatives,rows,List.flatMap_nil,stream,List.append_nil,
    List.reverse_nil,List.nil_append]
   change (QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.next search)^[2*(q+1)+C.tail.length+4]
    (some (QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.cfg search 0 false none (qword q) [] [] C []))=
    some ((QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.machine search).halt C.tail.reverse)
   exact hr
  refine {hh with steps_le_m:=hh.steps_le_m.trans ?_}
  have htail:C.tail.length≤ C.length:=by simp only [List.length_tail];omega
  have hs:(q+1)+C.length≤ L:=by
   simpa only [stateSize,rows,List.flatMap_nil,stream,List.append_nil,qword_length] using hsize
  simp only [List.length_nil,Nat.zero_add,Nat.one_mul,callBudget]
  omega
 |cons A R ih=>
  have hi:=invocationExec q A R C
  have ht:=ih (pushed (found q A R) (stream (coords q A)) C) ((stateSize_next q A R C).trans hsize)
  have hs:(q+1)+(stream (coords q A)).length+(rows q R).length+C.length≤ L:=by
   rwa [stateSize_cons] at hsize
  have hin:(QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.input q A R).length≤ L:=by
   rw [input_eq,rows_cons]
   simp only [List.length_append,qword_length]
   omega
  have hm:=Composition.polynomial_eval_monotone retainedSearchTime hin
  dsimp only at hm
  have hc:EvalsToInTime (TM2.step machine.program) (state q (A::R) C)
   (some (state q R (pushed (found q A R) (stream (coords q A)) C))) (callBudget L):=by
   refine {hi with steps_le_m:=hi.steps_le_m.trans ?_}
   dsimp only [callBudget]
   omega
  have hh:=EvalsToInTime.trans (TM2.step machine.program) _ _ _ _ _ hc ht
  rw [←collected_cons] at hh
  have he:(R.length+1)*callBudget L+callBudget L=((A::R).length+1)*callBudget L:=by
   simp only [List.length_cons];ring
  rwa [he] at hh
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def time:Polynomial ℕ:=(Polynomial.X+1)*(retainedSearchTime+Polynomial.C 10*Polynomial.X+Polynomial.C 10)
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def execute (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step machine.program) (state q R [])
  (some (machine.halt (rows q (representatives q R)).reverse.tail.reverse))
  (time.eval (qword q++rows q R).length):=by
 let L:=(qword q++rows q R).length
 have h0:=executeAux q L R [] (by simp [stateSize,L])
 have h:EvalsToInTime (TM2.step machine.program) (state q R [])
  (some (machine.halt (rows q (representatives q R)).reverse.tail.reverse)) ((R.length+1)*callBudget L):=by
  simpa only [collected,List.append_nil] using h0
 have hc:R.length≤ L:=by
  have hs:=rows_count_bound q R
  dsimp [L];simp only [List.length_append];omega
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [time,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_C]
 change (R.length+1)*callBudget L≤(L+1)*callBudget L
 exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem init_eq (q:ℕ) (R:List SL(2,ZMod q)):
 machine.init (qword q++rows q R)=state q R []:=by
 simp [Machine.init,QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.machine,QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.machine,state,QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.cfg,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=search.input <;>by_cases ho:j=search.output <;>
  simp_all [DrainInput.tapes,Function.update,search_io,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem raw_final_output (q:ℕ) (R:List SL(2,ZMod q)):
 (rows q R).reverse.tail.reverse=raw (R.flatMap (coords q)):=by
 simp only [rows,List.tail_reverse,List.reverse_reverse,raw]
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def rawExec (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step machine.program) (machine.init (qword q++rows q R))
  (some (machine.halt (raw ((representatives q R).flatMap (coords q)))))
  (time.eval (qword q++rows q R).length):=by
 have h:=execute q R
 rw [←init_eq,raw_final_output] at h
 exact h
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem original_output_source (q:ℕ) [Fact q.Prime]:
 (representatives q (lpsSLList q)).map (quotient q)=lpsPSLList q:=mapped_original_representatives q
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def composeRuns (A B:Machine) (x y z:List Bool) (p r:Polynomial ℕ)
 (hA:EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt y)) (p.eval x.length))
 (hB:EvalsToInTime (TM2.step B.program) (B.init y) (some (B.halt z)) (r.eval y.length)):
 EvalsToInTime (TM2.step (Composition.machine A B).program) ((Composition.machine A B).init x)
  (some ((Composition.machine A B).halt z)) ((Composition.timePolynomial A p r).eval x.length):=by
 have hL:y.length≤(Composition.intermediateLengthPolynomial A p).eval x.length:=by
  simpa [Composition.intermediateLengthPolynomial,Nat.mul_comm] using Machine.output_length_le A x y _ hA
 have hr:=Composition.polynomial_eval_monotone r hL
 have hh:=Composition.executes A B x y z _ _ hA hB
 refine {hh with steps_le_m:=hh.steps_le_m.trans ?_}
 simp only [Composition.timePolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C]
 exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hr (Nat.mul_le_mul_left 2 hL)) 2) _
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
abbrev Input:={q:ℕ//q.Prime}
instance (a:Input):Fact a.val.Prime:=⟨a.property⟩
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def sl:=LPSOriginalSLListMachine.machine
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def switch:=QEC.Coding.BitTuring.BooleanSwitch.machine sl sl
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def switchTime:Polynomial ℕ:=LPSOriginalSLListMachine.time+Polynomial.C 2
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem sl_io:sl.input≠sl.output:=by simp [sl,LPSOriginalSLListMachine.machine,Composition.machine]
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def switchExec (a:Input):
 EvalsToInTime (TM2.step switch.program) (switch.init (false::unary a.val))
  (some (switch.halt (LPSOriginalSLListMachine.output a.val))) (switchTime.eval (false::unary a.val).length):=by
 have h:=QEC.Coding.BitTuring.BooleanSwitch.execB sl sl sl_io sl_io (unary a.val) _ _
  (LPSOriginalSLListMachine.exec a.val a.property.one_lt)
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hm:=Composition.polynomial_eval_monotone LPSOriginalSLListMachine.time
  (show (unary a.val).length≤(false::unary a.val).length by simp)
 dsimp only at hm
 simp only [switchTime,Polynomial.eval_add,Polynomial.eval_C]
 omega
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def markReverse:=Composition.machine BitDelimiter.machine BitReverse.machine
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def markReverseTime:Polynomial ℕ:=
 Composition.timePolynomial BitDelimiter.machine (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (Polynomial.X+1)
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def markReverseExec (w:List Bool):
 EvalsToInTime (TM2.step markReverse.program) (markReverse.init w)
  (some (markReverse.halt (w++[false]).reverse)) (markReverseTime.eval w.length):=by
 have hd:=BitDelimiter.exec w
 have hr:=BitReverse.exec (w++[false])
 exact composeRuns BitDelimiter.machine BitReverse.machine w (w++[false]) _
  (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (Polynomial.X+1)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using hd)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using hr)
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem original_fields_nonempty (a:Input):
 (lpsSLList a.val).flatMap (coords a.val)≠[]:=by
 have hm:=mem_lpsSLList a.val (1:SL(2,ZMod a.val))
 intro he
 have hh:∀A∈lpsSLList a.val,coords a.val A=[]:=List.flatMap_eq_nil_iff.mp he
 have hz:=hh 1 hm
 simp [coords,LPSMatrixProductMachine.fields] at hz
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem marked_source (a:Input):
 LPSOriginalSLListMachine.output a.val++[false]=rows a.val (lpsSLList a.val):=by
 change raw ((lpsSLList a.val).flatMap (coords a.val))++[false]=_
 rw [MatrixListQuery.delimiter_raw _ (original_fields_nonempty a)]
 rfl
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def reverseBody:=Composition.machine switch markReverse
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def reverseTime:Polynomial ℕ:=Composition.timePolynomial switch switchTime markReverseTime
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def reverseBodyExec (a:Input):
 EvalsToInTime (TM2.step reverseBody.program) (reverseBody.init (false::unary a.val))
  (some (reverseBody.halt (rows a.val (lpsSLList a.val)).reverse)) (reverseTime.eval (false::unary a.val).length):=by
 have hm:=markReverseExec (LPSOriginalSLListMachine.output a.val)
 rw [marked_source a] at hm
 exact composeRuns switch markReverse _ _ _ switchTime markReverseTime (switchExec a) hm
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def retain:=RetainedInput.machine reverseBody
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def retainTime:Polynomial ℕ:=RetainedInput.timePolynomial reverseBody reverseTime
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def retainExec (a:Input):
 EvalsToInTime (TM2.step retain.program) (retain.init (false::unary a.val))
  (some (retain.halt ((rows a.val (lpsSLList a.val)).reverse++false::unary a.val)))
  (retainTime.eval (false::unary a.val).length):=
 RetainedInput.executes_polynomial reverseBody (fun a:Input=>false::unary a.val)
  (fun a=> (rows a.val (lpsSLList a.val)).reverse) reverseTime reverseBodyExec a
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def restore:=Composition.machine retain BitReverse.machine
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def restoreTime:Polynomial ℕ:=Composition.timePolynomial retain retainTime (Polynomial.X+1)
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def restoreExec (a:Input):
 EvalsToInTime (TM2.step restore.program) (restore.init (false::unary a.val))
  (some (restore.halt (qword a.val++rows a.val (lpsSLList a.val))))
  (restoreTime.eval (false::unary a.val).length):=by
 have hr:=BitReverse.exec ((rows a.val (lpsSLList a.val)).reverse++false::unary a.val)
 have he:((rows a.val (lpsSLList a.val)).reverse++false::unary a.val).reverse=
  qword a.val++rows a.val (lpsSLList a.val):=by
  simp [qword,unary,List.reverse_append,List.reverse_cons,List.append_assoc]
 rw [he] at hr
 exact composeRuns retain BitReverse.machine _ _ _ retainTime (Polynomial.X+1) (retainExec a)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using hr)
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def machine:=Composition.machine (FixedLiteral.prefixMachine [false]) restore
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def time:Polynomial ℕ:=
 Composition.timePolynomial (FixedLiteral.prefixMachine [false]) (FixedLiteral.prefixTime [false]) restoreTime
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.val))
  (some (machine.halt (qword a.val++rows a.val (lpsSLList a.val)))) (time.eval (unary a.val).length):=by
 have hp:=FixedLiteral.prefixExec [false] (unary a.val)
 exact composeRuns (FixedLiteral.prefixMachine [false]) restore _ _ _ (FixedLiteral.prefixTime [false]) restoreTime hp (restoreExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
abbrev Input:=QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.Input
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def input (a:Input):List Bool:=unary a.val
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def output (q:ℕ) [Fact q.Prime]:List Bool:=
 raw ((QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.representatives q (lpsSLList q)).flatMap (QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.coords q))
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
def machine:=Composition.machine QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.machine QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.machine
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def time:Polynomial ℕ:=Composition.timePolynomial QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.machine
 QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.time QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.time
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
  (some (machine.halt (output a.val))) (time.eval (input a).length):=by
 have hi:=QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.exec a
 have hf:=QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.rawExec a.val (lpsSLList a.val)
 exact QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.composeRuns QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.machine QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.machine
  _ _ _ QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.time QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.time hi hf
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem input_injective:Function.Injective input:=by
 intro a b hh
 apply Subtype.ext
 have h:=congrArg List.length hh
 simpa only [input,unary_length] using h
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
theorem original_source (a:Input):
 (QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.representatives a.val (lpsSLList a.val)).map (QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.quotient a.val)=lpsPSLList a.val:=
 QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.mapped_original_representatives a.val
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def outputsInTime (a:Input):
 TM2OutputsInTime machine.toFinTM2 (input a) (some (output a.val)) (time.eval (input a).length):=
 Machine.outputsInTime machine _ _ _ (exec a)
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def computableInPolyTime:
 TM2ComputableInPolyTime input id (fun a:Input=>output a.val) where
 tm:=machine.toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time
 outputsFun:=fun a=>by
  change TM2OutputsInTime machine.toFinTM2 (List.map id (input a))
   (some (List.map id (output a.val))) (time.eval (input a).length)
  have h:=outputsInTime a
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
  (some (machine.halt (output a.q))) (time.eval (2*Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨a.q,a.prime⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 change time.eval (unary a.q).length≤ time.eval (2*Fintype.card PSL(2,ZMod a.q))
 rw [unary_length]
 exact Composition.polynomial_eval_monotone time a.q_le_two_mul_card_psl
/-- Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p):
 TM2OutputsInTime machine.toFinTM2 (unary a.q) (some (output a.q))
  (time.eval (2*Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine
