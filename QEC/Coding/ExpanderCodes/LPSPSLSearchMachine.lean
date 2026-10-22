import QEC.Coding.BitTuring.BooleanSwitch
import QEC.Coding.BitTuring.UnarySuffixEmpty
import QEC.Coding.BitTuring.UnaryTailProjection
import QEC.Coding.BitTuring.FlagLoop
import QEC.Coding.BitTuring.FixedLiteral
import QEC.Coding.ExpanderCodes.LPSPSLEqualityMachine
import QEC.Coding.ExpanderCodes.LPSRetainedPrefixQueries

/-!
# Actual search for later original PSL representatives

Original forward matrix fields drive actual projection, reversal, delimiter and PSL equality instructions. Simultaneous entry reversal preserves sign equality; the original quotient predicate fixes the source convention. Real EOF/match/drop branches feed a terminating flag loop with complete retained-input execution and polynomial bounds. No-later-match representative recursion maps to the original LAST-occurrence list dedup as exact lists, including characteristic two. This search is consumed by the complete q-only PSL-list program.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def coords (q:ℕ) (A:SL(2,ZMod q)):List ℕ:=LPSMatrixProductMachine.fields q A.val
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def header (q:ℕ) (A:SL(2,ZMod q)):List ℕ:=q::coords q A
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def rows (q:ℕ) (R:List SL(2,ZMod q)):List Bool:=stream (R.flatMap (coords q))
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def input (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):List Bool:=stream (header q A)++rows q R
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def matchFlag (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)):Bool:=
 letI:=lpsPSLDecidableEq q
 decide ((QuotientGroup.mk B:PSL(2,ZMod q))=QuotientGroup.mk A)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem reverse_raw_header (q a b c d e f g h:ℕ):
 (raw [q,d,c,b,a,h,g,f,e]).reverse=raw [e,f,g,h,a,b,c,d,q]:=by
 have h0:=raw_append_last [q,d,c,b,a,h,g,f] e
 have h1:=raw_append_last [e,f,g,h,a,b,c,d] q
 change (raw ([q,d,c,b,a,h,g,f]++[e])).reverse=raw ([e,f,g,h,a,b,c,d]++[q])
 rw [h0,h1]
 simp [stream,unary,List.reverse_append,List.reverse_cons,List.append_assoc]
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem result_reverse (a b c d e f g h q:ℕ):
 PSLComparison.result d c b a h g f e q=PSLComparison.result a b c d e f g h q:=by
 simp only [PSLComparison.result,Bool.and_assoc,Bool.and_comm]
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def queryBody:=Composition.machine BitReverse.machine
 (Composition.machine BitDelimiter.machine PSLComparison.predicateMachine)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def queryMachine:=RetainedInput.machine
 (Composition.machine (PrefixProjection.prefixMachine 8 (PrefixProjection.allMask 8)) queryBody)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def queryTime:Polynomial ℕ:=PSLComparison.time+Polynomial.C 30*(Polynomial.X+1)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def queryExec (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) (s:List Bool):
 EvalsToInTime (TM2.step queryMachine.program)
  (queryMachine.init (stream (header q A++coords q B)++s))
  (some (queryMachine.halt (matchFlag q A B::(stream (header q A++coords q B)++s))))
  (queryTime.eval (stream (header q A++coords q B)++s).length):=by
 let xs:=header q A++coords q B
 let ys:=(LPSMatrixProductMachine.fields q B.val).reverse++(LPSMatrixProductMachine.fields q A.val).reverse++[q]
 have hp:=PrefixProjection.polyExec 8 (PrefixProjection.allMask 8) xs
  (by simp [xs,header,coords,LPSMatrixProductMachine.fields]) s
 rw [PrefixProjection.fields_all] at hp
 have hb:=BitReverse.exec (raw xs)
 have hre:(raw xs).reverse=raw ys:=by
  simpa [xs,ys,header,coords,LPSMatrixProductMachine.fields] using
   reverse_raw_header q (A.val 1 1).val (A.val 1 0).val (A.val 0 1).val (A.val 0 0).val
    (B.val 1 1).val (B.val 1 0).val (B.val 0 1).val (B.val 0 0).val
 rw [hre] at hb
 have hd:=BitDelimiter.exec (raw ys)
 rw [MatrixListQuery.delimiter_raw ys (by simp [ys,LPSMatrixProductMachine.fields])] at hd
 let : NeZero q:=⟨(Fact.out:q.Prime).ne_zero⟩
 have ha:=PSLComparison.polyExec (B.val 1 1).val (B.val 1 0).val (B.val 0 1).val (B.val 0 0).val
  (A.val 1 1).val (A.val 1 0).val (A.val 0 1).val (A.val 0 0).val q
  (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
 have hflag:PSLComparison.result (B.val 1 1).val (B.val 1 0).val (B.val 0 1).val (B.val 0 0).val
    (A.val 1 1).val (A.val 1 0).val (A.val 0 1).val (A.val 0 0).val q=matchFlag q A B:=by
  rw [result_reverse]
  have hs:=LPSPSLEqualityMachine.result_eq_source q B A
  change [PSLComparison.result (B.val 0 0).val (B.val 0 1).val (B.val 1 0).val (B.val 1 1).val
   (A.val 0 0).val (A.val 0 1).val (A.val 1 0).val (A.val 1 1).val q]=[matchFlag q A B] at hs
  simpa only [List.cons.injEq,and_true] using hs
 rw [hflag] at ha
 change EvalsToInTime _ _ (some (PSLComparison.predicateMachine.halt [matchFlag q A B]))
  (PSLComparison.time.eval (stream ys).length) at ha
 have hc:=Composition.executes BitDelimiter.machine PSLComparison.predicateMachine _ _ _ _ _ hd ha
 have hbc:=Composition.executes BitReverse.machine
  (Composition.machine BitDelimiter.machine PSLComparison.predicateMachine) _ _ _ _ _ hb hc
 have hpc:=Composition.executes (PrefixProjection.prefixMachine 8 (PrefixProjection.allMask 8)) queryBody _ _ _ _ _ hp hbc
 have hr:=RetainedInput.executes
  (Composition.machine (PrefixProjection.prefixMachine 8 (PrefixProjection.allMask 8)) queryBody) _ _ _ hpc
 refine {hr with steps_le_m:=hr.steps_le_m.trans ?_}
 have hy:(stream ys).length=(stream xs).length:=by
  simp only [xs,ys,header,coords,LPSMatrixProductMachine.fields,List.reverse_cons,List.reverse_nil,List.nil_append,
   List.cons_append,List.nil_append,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
 have hpmono:=Composition.polynomial_eval_monotone PSLComparison.time
  (show (stream ys).length≤(stream xs++s).length by rw [hy];simp)
 simp only [List.length_append] at hpmono
 have hxr:=raw_length_le xs
 have hyr:=raw_length_le ys
 change _≤ queryTime.eval (stream xs++s).length
 simp only [PrefixProjection.time,queryTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,Polynomial.eval_one,List.length_cons,List.length_nil,List.length_append]
 omega
end QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
namespace QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem rows_cons (q:ℕ) (B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 rows q (B::R)=stream (coords q B)++rows q R:=by
 simp only [rows,List.flatMap_cons,MatrixListQuery.stream_append]
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem input_cons (q:ℕ) (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 input q A (B::R)=stream (header q A++coords q B)++rows q R:=by
 simp only [input,rows_cons,MatrixListQuery.stream_append,List.append_assoc]
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem input_tail_le (q:ℕ) (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 (input q A R).length≤(input q A (B::R)).length:=by
 simp only [input,rows_cons,List.length_append]
 omega
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem rows_cons_nonempty (q:ℕ) (B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 (rows q (B::R)).isEmpty=false:=by
 have hl:0<(rows q (B::R)).length:=by
  simp only [rows_cons,List.length_append,coords,LPSMatrixProductMachine.fields,stream_length,
   List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega
 cases he:rows q (B::R) with
 |nil=>simp [he] at hl
 |cons b bs=>rfl
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def keepHead (k:Fin 9):Bool:=decide (k.val<5)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def dropMachine:=QEC.Coding.BitTuring.UnaryArithmetic.TailProjection.machine 8 keepHead
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem selected_header (q:ℕ) (A B:SL(2,ZMod q)):
 fields 8 keepHead 0 (header q A++coords q B)=header q A:=by
 simp [header,coords,LPSMatrixProductMachine.fields,fields,maskAt,keepHead]
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def dropExec (q:ℕ) (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step dropMachine.program) (dropMachine.init (input q A (B::R)))
  (some (dropMachine.halt (input q A R))) (6*((input q A (B::R)).length+1)):=by
 have h:=QEC.Coding.BitTuring.UnaryArithmetic.TailProjection.streamExec 8 keepHead (header q A++coords q B)
  (by simp [header,coords,LPSMatrixProductMachine.fields]) (rows q R)
  (by rw [selected_header];simp [header])
 rw [selected_header] at h
 rw [input_cons]
 simp only [QEC.Coding.BitTuring.UnaryArithmetic.TailProjection.time,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] at h
 exact h
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def declinedMachine:=Composition.machine dropMachine (FixedLiteral.prefixMachine [false])
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def matchDispatch:=QEC.Coding.BitTuring.BooleanSwitch.machine (FixedLiteral.machine [true,true]) declinedMachine
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def matchDispatchExec (q:ℕ) (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)) (f:Bool):
 EvalsToInTime (TM2.step matchDispatch.program) (matchDispatch.init (f::input q A (B::R)))
  (some (matchDispatch.halt (if f then [true,true] else false::input q A R)))
  (12*(input q A (B::R)).length+20):=by
 cases f with
 |true=>
  have h:=QEC.Coding.BitTuring.BooleanSwitch.execA (FixedLiteral.machine [true,true]) declinedMachine _ _ _
   (FixedLiteral.exec [true,true] (input q A (B::R)))
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  omega
 |false=>
  have hd:=dropExec q A B R
  have hp:=FixedLiteral.prefixExec [false] (input q A R)
  have hc:=Composition.executes dropMachine (FixedLiteral.prefixMachine [false]) _ _ _ _ _ hd hp
  have h:=QEC.Coding.BitTuring.BooleanSwitch.execB (FixedLiteral.machine [true,true]) declinedMachine
   (by change (0:Fin 2)≠1;decide)
   (by simp [declinedMachine,Composition.machine]) _ _ _ hc
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hl:=input_tail_le q A B R
  simp only [FixedLiteral.prefixTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_X,List.length_cons,List.length_nil]
  omega
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def compareMachine:=Composition.machine queryMachine matchDispatch
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def compareExec (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step compareMachine.program) (compareMachine.init (input q A (B::R)))
  (some (compareMachine.halt (if matchFlag q A B then [true,true] else false::input q A R)))
  (queryTime.eval (input q A (B::R)).length+14*(input q A (B::R)).length+24):=by
 have hq:=queryExec q A B (rows q R)
 rw [←input_cons] at hq
 have hs:=matchDispatchExec q A B R (matchFlag q A B)
 have h:=Composition.executes queryMachine matchDispatch _ _ _ _ _ hq hs
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [List.length_cons]
 omega
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def emptyQuery:=RetainedInput.machine (SuffixEmpty.machine 5)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def emptyQueryExec (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step emptyQuery.program) (emptyQuery.init (input q A R))
  (some (emptyQuery.halt ((rows q R).isEmpty::input q A R))) (4*(input q A R).length+11):=by
 have h:=RetainedInput.executes (SuffixEmpty.machine 5) _ _ _
  (SuffixEmpty.exec 5 (header q A) (rows q R) (by simp [header,coords,LPSMatrixProductMachine.fields]))
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 change (input q A R).length+3+3*(input q A R).length+2*[((rows q R).isEmpty)].length+6≤ _
 simp only [List.length_cons,List.length_nil]
 omega
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def emptyDispatch:=QEC.Coding.BitTuring.BooleanSwitch.machine (FixedLiteral.machine [true,false]) compareMachine
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def bodyMachine:=Composition.machine emptyQuery emptyDispatch
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def bodyTime:Polynomial ℕ:=PSLComparison.time+Polynomial.C 100*(Polynomial.X+1)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def bodyEmptyExec (q:ℕ) (A:SL(2,ZMod q)):
 EvalsToInTime (TM2.step bodyMachine.program) (bodyMachine.init (input q A []))
  (some (bodyMachine.halt [true,false])) (bodyTime.eval (input q A []).length):=by
 have he:=emptyQueryExec q A []
 have hd:=QEC.Coding.BitTuring.BooleanSwitch.execA (FixedLiteral.machine [true,false]) compareMachine _ _ _
  (FixedLiteral.exec [true,false] (input q A []))
 change EvalsToInTime _ _ (some (emptyQuery.halt (true::input q A []))) _ at he
 have h:=Composition.executes emptyQuery emptyDispatch _ _ _ _ _ he hd
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [bodyTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,Polynomial.eval_one,List.length_cons]
 omega
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def bodyConsExec (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step bodyMachine.program) (bodyMachine.init (input q A (B::R)))
  (some (bodyMachine.halt (if matchFlag q A B then [true,true] else false::input q A R)))
  (bodyTime.eval (input q A (B::R)).length):=by
 have he:=emptyQueryExec q A (B::R)
 rw [rows_cons_nonempty] at he
 have hc:=compareExec q A B R
 have hd:=QEC.Coding.BitTuring.BooleanSwitch.execB (FixedLiteral.machine [true,false]) compareMachine
  (by change (0:Fin 2)≠1;decide)
  (by simp [compareMachine,Composition.machine]) _ _ _ hc
 have h:=Composition.executes emptyQuery emptyDispatch _ _ _ _ _ he hd
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [bodyTime,queryTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,Polynomial.eval_one,List.length_cons]
 omega
end QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
namespace QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def searchMachine:=FlagLoop.machine bodyMachine
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def found (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):Bool:=R.any (matchFlag q A)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def callBudget (L:ℕ):ℕ:=bodyTime.eval L+2*L+4
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem input_pos (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 1≤(input q A R).length:=by
 simp only [input,List.length_append,header,coords,LPSMatrixProductMachine.fields,
  stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
 omega
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem rows_count_bound (q:ℕ) (R:List SL(2,ZMod q)):R.length≤(rows q R).length:=by
 induction R with
 |nil=>simp [rows,stream]
 |cons B R ih=>
  simp only [List.length_cons,rows_cons,List.length_append]
  have hl:1≤(stream (coords q B)).length:=by
   simp only [coords,LPSMatrixProductMachine.fields,stream_length,
    List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  omega
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def searchExecAux (q L:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q))
 (hsize:(input q A R).length≤ L) (hpos:1≤ L):
 EvalsToInTime (TM2.step searchMachine.program) (searchMachine.init (input q A R))
  (some (searchMachine.halt [found q A R])) ((R.length+1)*callBudget L):=by
 induction R with
 |nil=>
  have hb:=bodyEmptyExec q A
  have h:=FlagLoop.invocationExec bodyMachine (by simp [bodyMachine,Composition.machine])
   (input q A []) [false] true _ hb
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hm:=Composition.polynomial_eval_monotone bodyTime hsize
  dsimp only at hm
  simp only [List.length_cons,List.length_nil,callBudget,Nat.one_mul,Nat.zero_add]
  omega
 |cons B R ih=>
  have hb:=bodyConsExec q A B R
  cases hf:matchFlag q A B with
  |true=>
   rw [hf] at hb
   simp only [found,List.any_cons,hf,Bool.true_or]
   have h:=FlagLoop.invocationExec bodyMachine (by simp [bodyMachine,Composition.machine])
    (input q A (B::R)) [true] true _ hb
   refine {h with steps_le_m:=h.steps_le_m.trans ?_}
   have hm:=Composition.polynomial_eval_monotone bodyTime hsize
   dsimp only at hm
   have h0:bodyTime.eval (input q A (B::R)).length+2*[true].length+4≤ callBudget L:=by
    simp only [List.length_cons,List.length_nil,callBudget];omega
   have hmul:callBudget L≤((B::R).length+1)*callBudget L:=by
    simp only [List.length_cons];nlinarith
   exact h0.trans hmul
  |false=>
   rw [hf] at hb
   have h0:=FlagLoop.invocationExec bodyMachine (by simp [bodyMachine,Composition.machine])
    (input q A (B::R)) (input q A R) false _ hb
   have hs:(input q A R).length≤ L:=(input_tail_le q A B R).trans hsize
   have ht:=ih hs
   have hc:EvalsToInTime (TM2.step searchMachine.program) (searchMachine.init (input q A (B::R)))
     (some (searchMachine.init (input q A R))) (callBudget L):=by
    refine {h0 with steps_le_m:=h0.steps_le_m.trans ?_}
    have hm:=Composition.polynomial_eval_monotone bodyTime hsize
    dsimp only at hm
    simp only [callBudget];omega
   have h:=EvalsToInTime.trans (TM2.step searchMachine.program) _ _ _ _ _ hc ht
   have he:(R.length+1)*callBudget L+callBudget L=((B::R).length+1)*callBudget L:=by
    simp only [List.length_cons];ring
   rw [he] at h
   simpa only [found,List.any_cons,hf,Bool.false_or] using h
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def searchTime:Polynomial ℕ:=(Polynomial.X+1)*(bodyTime+Polynomial.C 2*Polynomial.X+Polynomial.C 4)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def searchExec (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step searchMachine.program) (searchMachine.init (input q A R))
  (some (searchMachine.halt [found q A R])) (searchTime.eval (input q A R).length):=by
 have h:=searchExecAux q (input q A R).length A R (le_refl _) (input_pos q A R)
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hl:R.length≤(input q A R).length:=by
  have hr:=rows_count_bound q R
  simp only [input,List.length_append];omega
 have hm:=Nat.mul_le_mul_right (callBudget (input q A R).length) (Nat.add_le_add_right hl 1)
 simpa only [searchTime,callBudget,Polynomial.eval_mul,Polynomial.eval_add,
  Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one] using hm
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def retainedSearchMachine:=RetainedInput.machine searchMachine
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def retainedSearchTime:Polynomial ℕ:=searchTime+Polynomial.C 3*Polynomial.X+Polynomial.C 8
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def retainedSearchExec (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step retainedSearchMachine.program) (retainedSearchMachine.init (input q A R))
  (some (retainedSearchMachine.halt (found q A R::input q A R)))
  (retainedSearchTime.eval (input q A R).length):=by
 have h:=RetainedInput.executes searchMachine _ _ _ (searchExec q A R)
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [retainedSearchTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,List.length_cons,List.length_nil]
 omega
end QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
namespace QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def quotient (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)):PSL(2,ZMod q):=QuotientGroup.mk A
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem found_iff (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 found q A R=true ↔ quotient q A∈R.map (quotient q):=by
 let :=lpsPSLDecidableEq q
 simp [found,matchFlag,quotient,List.any_eq_true,List.mem_map]
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
def representatives (q:ℕ) [Fact q.Prime]:List SL(2,ZMod q)→List SL(2,ZMod q)
 | [] => []
 | A::R =>if found q A R then representatives q R else A::representatives q R
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem mapped_representatives (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)):
 let :=lpsPSLDecidableEq q
 (representatives q R).map (quotient q)=(R.map (quotient q)).dedup:=by
 let :=lpsPSLDecidableEq q
 induction R with
 |nil=>simp [representatives]
 |cons A R ih=>
  cases hf:found q A R with
  |true=>
   have hm:quotient q A∈R.map (quotient q):=(found_iff q A R).mp hf
   simp only [representatives,hf,↓reduceIte,List.map_cons,List.dedup_cons_of_mem hm,ih]
  |false=>
   have hm:quotient q A∉R.map (quotient q):=by
    intro hh
    have ht:=(found_iff q A R).mpr hh
    rw [hf] at ht;cases ht
   simp only [representatives,hf,Bool.false_eq_true,↓reduceIte,List.map_cons,List.dedup_cons_of_notMem hm,ih]
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem mapped_original_representatives (q:ℕ) [Fact q.Prime]:
 (representatives q (lpsSLList q)).map (quotient q)=lpsPSLList q:=mapped_representatives q _
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem rows_injective (q:ℕ) (hq:0<q):Function.Injective (rows q):=by
 intro R S hh
 have he:=stream_injective hh
 clear hh
 induction R generalizing S with
 |nil=>
  cases S with
  |nil=>rfl
  |cons B S=>
   simp only [List.flatMap_nil,List.flatMap_cons,coords,LPSMatrixProductMachine.fields,
    List.cons_append,List.nil_append] at he
   cases he
 |cons A R ih=>
  cases S with
  |nil=>
   simp only [List.flatMap_nil,List.flatMap_cons,coords,LPSMatrixProductMachine.fields,
    List.cons_append,List.nil_append] at he
   cases he
  |cons B S=>
   simp only [List.flatMap_cons,coords,LPSMatrixProductMachine.fields,List.cons_append,List.nil_append,List.cons.injEq] at he
   rcases he with ⟨h00,h01,h10,h11,ht⟩
   have hab:A=B:=by
    apply Subtype.ext
    exact LPSMatrixProductMachine.fields_injective q hq
     (by simp [LPSMatrixProductMachine.fields,h00,h01,h10,h11])
   have hrs:R=S:=ih (S:=S) (by simpa only [coords] using ht)
   simp only [hab,hrs]
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
theorem input_injective (q:ℕ) (hq:0<q):
 Function.Injective (fun x:SL(2,ZMod q)×List SL(2,ZMod q)=>input q x.1 x.2):=by
 intro x y hh
 have he:=PrefixProjection.stream_suffix_injective (header q x.1) (header q y.1)
  (rows q x.2) (rows q y.2) (by simp [header,coords,LPSMatrixProductMachine.fields]) hh
 have ha:x.1=y.1:=by
  apply Subtype.ext
  have hf:coords q x.1=coords q y.1:=List.cons.inj he.1 |>.2
  exact LPSMatrixProductMachine.fields_injective q hq hf
 exact Prod.ext ha (rows_injective q hq he.2)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def searchOutputsInTime (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 TM2OutputsInTime searchMachine.toFinTM2 (input q A R) (some [found q A R])
  (searchTime.eval (input q A R).length):=Machine.outputsInTime searchMachine _ _ _ (searchExec q A R)
/-- Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate. -/
noncomputable def searchComputableInPolyTime (q:ℕ) [Fact q.Prime]:
 TM2ComputableInPolyTime (fun x:SL(2,ZMod q)×List SL(2,ZMod q)=>input q x.1 x.2)
  id (fun x=>[found q x.1 x.2]) where
 tm:=searchMachine.toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=searchTime
 outputsFun:=fun x=>by
  change TM2OutputsInTime searchMachine.toFinTM2 (List.map id (input q x.1 x.2))
   (some (List.map id [found q x.1 x.2])) (searchTime.eval (input q x.1 x.2).length)
  have h:=searchOutputsInTime q x.1 x.2
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
end QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
