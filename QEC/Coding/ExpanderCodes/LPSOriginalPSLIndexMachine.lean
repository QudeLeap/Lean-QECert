import QEC.Coding.BitTuring.CountedFlagLoop
import QEC.Coding.ExpanderCodes.LPSOriginalPSLListMachine

/-!
# Actual original PSL index program

One fixed finite tape program reads only prime q and four canonical matrix fields.
It generates its own original LAST-occurrence PSL representatives, preserves the
query header and counts actual mismatches until the first quotient match. Exact
source-list equality identifies its unary output with lpsPSLEnumerationEquiv.symm.
Counted whole execution, faithful input, standard Mathlib polynomial computation
and a genuine residue-prime PSL carrier budget are proved. Ordered lookup, full
sparse CSS execution and unconditional strong centered-theta growth remain
obligations of the public PK22 theorem.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- First matching PSL quotient position, or row-count sentinel if absent. -/
def rowIndex (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)):List SL(2,ZMod q)→ℕ
 | []=>0
 | B::R=>if matchFlag q A B then 0 else rowIndex q A R+1
/-- The generic search ordinal never exceeds its row count. -/
theorem rowIndex_le (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 rowIndex q A R≤ R.length:=by
 induction R with
 | nil=>rfl
 | cons B R ih=>cases hf:matchFlag q A B <;> simp only [rowIndex,hf,Bool.false_eq_true,↓reduceIte,List.length_cons] <;> omega
/-- Instantiate the counted loop with the actual PSL match/EOF/drop body. -/
def indexedMachine:=CountedFlagLoop.machine bodyMachine
/-- Per-call bound for actual body, copies, tally and terminal cleanup. -/
noncomputable def callBudget (L H:ℕ):ℕ:=bodyTime.eval L+3*L+H+6
/-- Remaining-row induction with a counter-plus-row invariant counts every actual run. -/
noncomputable def indexedExecAux (q L H:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)) (n:ℕ)
 (hsize:(input q A R).length≤ L) (hcount:n+R.length≤ H) (hpos:1≤ L):
 EvalsToInTime (TM2.step (CountedFlagLoop.program bodyMachine))
  (CountedFlagLoop.start bodyMachine (input q A R) (unary n))
  (some (CountedFlagLoop.halt bodyMachine (unary (n+rowIndex q A R))))
  ((R.length+1)*callBudget L H):=by
 induction R generalizing n with
 | nil=>
  have hb:=bodyEmptyExec q A
  have h:=CountedFlagLoop.terminalExec bodyMachine (by simp [bodyMachine,Composition.machine])
   (input q A []) [false] (unary n) _ hb
  have hm:=Composition.polynomial_eval_monotone bodyTime hsize
  dsimp only at hm
  have hh:EvalsToInTime (TM2.step (CountedFlagLoop.program bodyMachine))
    (CountedFlagLoop.start bodyMachine (input q A []) (unary n))
    (some (CountedFlagLoop.halt bodyMachine (unary n).reverse)) (callBudget L H):=by
   refine {h with steps_le_m:=h.steps_le_m.trans ?_}
   simp only [List.length_cons,List.length_nil,unary_length,callBudget]
   simp only [List.length_nil,Nat.add_zero] at hcount
   omega
  simpa only [rowIndex,Nat.add_zero,List.length_nil,Nat.zero_add,Nat.one_mul,unary,List.reverse_replicate] using hh
 | cons B R ih=>
  have hb:=bodyConsExec q A B R
  have hm:=Composition.polynomial_eval_monotone bodyTime hsize
  dsimp only at hm
  cases hf:matchFlag q A B with
  | true=>
   rw [hf] at hb
   have h:=CountedFlagLoop.terminalExec bodyMachine (by simp [bodyMachine,Composition.machine])
    (input q A (B::R)) [true] (unary n) _ hb
   have hh:EvalsToInTime (TM2.step (CountedFlagLoop.program bodyMachine))
    (CountedFlagLoop.start bodyMachine (input q A (B::R)) (unary n))
    (some (CountedFlagLoop.halt bodyMachine (unary n).reverse)) (((B::R).length+1)*callBudget L H):=by
    refine {h with steps_le_m:=h.steps_le_m.trans ?_}
    have hc:bodyTime.eval (input q A (B::R)).length+3*[true].length+(unary n).length+6≤ callBudget L H:=by
     simp only [List.length_cons,List.length_nil,unary_length,callBudget]
     simp only [List.length_cons] at hcount
     omega
    have hp:callBudget L H≤((B::R).length+1)*callBudget L H:=by simp only [List.length_cons];nlinarith
    exact hc.trans hp
   simpa only [rowIndex,hf,↓reduceIte,Nat.add_zero,unary,List.reverse_replicate] using hh
  | false=>
   rw [hf] at hb
   have h:=CountedFlagLoop.continueExec bodyMachine (by simp [bodyMachine,Composition.machine])
    (input q A (B::R)) (input q A R) (unary n) _ hb
   have hs:(input q A R).length≤ L:=(input_tail_le q A B R).trans hsize
   have hn:n+1+R.length≤ H:=by simp only [List.length_cons] at hcount;omega
   have ht:=ih (n+1) hs hn
   have he:true::unary n=unary (n+1):=by simp [unary,List.replicate_succ]
   rw [he] at h
   have hh:EvalsToInTime (TM2.step (CountedFlagLoop.program bodyMachine))
    (CountedFlagLoop.start bodyMachine (input q A (B::R)) (unary n))
    (some (CountedFlagLoop.start bodyMachine (input q A R) (unary (n+1)))) (callBudget L H):=by
    refine {h with steps_le_m:=h.steps_le_m.trans ?_}
    have hl:((input q A R).length)≤ L:=hs
    dsimp only [callBudget]
    omega
   have hc:=EvalsToInTime.trans (TM2.step (CountedFlagLoop.program bodyMachine))
    (callBudget L H) ((R.length+1)*callBudget L H)
    (CountedFlagLoop.start bodyMachine (input q A (B::R)) (unary n))
    (CountedFlagLoop.start bodyMachine (input q A R) (unary (n+1)))
    (some (CountedFlagLoop.halt bodyMachine (unary (n+1+rowIndex q A R)))) hh ht
   have heq:(R.length+1)*callBudget L H+callBudget L H=((B::R).length+1)*callBudget L H:=by simp only [List.length_cons];ring
   rw [heq] at hc
   simpa only [rowIndex,hf,Bool.false_eq_true,↓reduceIte,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- The computed first-match ordinal is the mapped quotient list index. -/
theorem rowIndex_idxOf (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 let :=lpsPSLDecidableEq q
 rowIndex q A R=(R.map (quotient q)).idxOf (quotient q A):=by
 let :=lpsPSLDecidableEq q
 induction R with
 | nil=>rfl
 | cons B R ih=>
  by_cases h:quotient q B=quotient q A
  · simp only [quotient] at h
    simp [rowIndex,matchFlag,quotient,h]
  · simp only [quotient] at h
    simp [rowIndex,matchFlag,quotient,h,ih]
/-- Original LAST representatives give exactly the original enumeration inverse index. -/
theorem original_source_index (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)):
 rowIndex q A (representatives q (lpsSLList q))=((lpsPSLEnumerationEquiv q).symm (quotient q A)).val:=by
 let :=lpsPSLDecidableEq q
 have h:=rowIndex_idxOf q A (representatives q (lpsSLList q))
 rw [mapped_original_representatives] at h
 change rowIndex q A (representatives q (lpsSLList q))=(lpsPSLList q).idxOf (quotient q A)
 exact h
/-- Original enumeration coverage rules out the missing-row sentinel. -/
theorem original_source_index_lt (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)):
 rowIndex q A (representatives q (lpsSLList q))<(representatives q (lpsSLList q)).length:=by
 have hl:(representatives q (lpsSLList q)).length=(lpsPSLList q).length:=by
  simpa only [List.length_map] using congrArg List.length (mapped_original_representatives q)
 rw [hl,original_source_index]
 exact ((lpsPSLEnumerationEquiv q).symm (quotient q A)).isLt
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Natural polynomial accounting for every row search and tally transfer. -/
noncomputable def indexedTime:Polynomial ℕ:=(Polynomial.X+1)*(bodyTime+Polynomial.C 4*Polynomial.X+Polynomial.C 6)
/-- Zero-counter actual query run returning its first-match unary index. -/
noncomputable def indexedExec (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step indexedMachine.program) (indexedMachine.init (input q A R))
  (some (indexedMachine.halt (unary (rowIndex q A R)))) (indexedTime.eval (input q A R).length):=by
 let L:=(input q A R).length
 have hc:R.length≤ L:=by
  have h:=rows_count_bound q R
  dsimp [L,input]
  simp only [List.length_append]
  omega
 have h:=indexedExecAux q L L A R 0 (by rfl) (by simpa only [Nat.zero_add] using hc) (input_pos q A R)
 have hb:EvalsToInTime (TM2.step (CountedFlagLoop.program bodyMachine))
  (CountedFlagLoop.start bodyMachine (input q A R) [])
  (some (CountedFlagLoop.halt bodyMachine (unary (rowIndex q A R))))
  (indexedTime.eval (input q A R).length):=by
  have he:callBudget L L=bodyTime.eval L+4*L+6:=by dsimp only [callBudget];omega
  have hm:=Nat.mul_le_mul_right (callBudget L L) (Nat.add_le_add_right hc 1)
  have hp:((R.length+1)*callBudget L L)≤ indexedTime.eval L:=by
   simpa only [indexedTime,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,he] using hm
  have hh: EvalsToInTime (TM2.step (CountedFlagLoop.program bodyMachine))
   (CountedFlagLoop.start bodyMachine (input q A R) (unary 0))
   (some (CountedFlagLoop.halt bodyMachine (unary (0+rowIndex q A R))))
   (indexedTime.eval L):={h with steps_le_m:=h.steps_le_m.trans hp}
  simpa only [unary,List.replicate_zero,Nat.zero_add] using hh
 rw [CountedFlagLoop.start_zero,CountedFlagLoop.halt_eq] at hb
 exact hb
/-- Standard Mathlib output certificate for the actual row query. -/
noncomputable def indexedOutputsInTime (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 TM2OutputsInTime indexedMachine.toFinTM2 (input q A R) (some (unary (rowIndex q A R)))
  (indexedTime.eval (input q A R).length):=
 Machine.outputsInTime indexedMachine _ _ _ (indexedExec q A R)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine.Initializer
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Only a prime modulus and a determinant-one matrix enter the initializer. -/
abbrev Input:=Σa:LPSOriginalPSLListMachine.Initializer.Input,SL(2,ZMod a.val)
instance (a:Input):Fact a.1.val.Prime:=⟨a.1.property⟩
/-- Encode reversed matrix coordinates followed by the prime modulus as five unary fields. -/
def input (a:Input):List Bool:=raw ((coords a.1.val a.2).reverse++[a.1.val])
/-- Separate the four reversed coordinate fields from the actual unary modulus. -/
theorem input_eq (a:Input):input a=stream (coords a.1.val a.2).reverse++unary a.1.val:=by
 exact raw_append_last _ _
/-- Bit reversal restores the forward query header encoding. -/
theorem input_reverse (a:Input):(input a).reverse=raw (header a.1.val a.2):=by
 have h0:=raw_append_last [(a.2.val 1 1).val,(a.2.val 1 0).val,(a.2.val 0 1).val,(a.2.val 0 0).val] a.1.val
 have h1:=raw_append_last [a.1.val,(a.2.val 0 0).val,(a.2.val 0 1).val,(a.2.val 1 0).val] (a.2.val 1 1).val
 change (raw ([(a.2.val 1 1).val,(a.2.val 1 0).val,(a.2.val 0 1).val,(a.2.val 0 0).val]++[a.1.val])).reverse=
  raw ([a.1.val,(a.2.val 0 0).val,(a.2.val 0 1).val,(a.2.val 1 0).val]++[(a.2.val 1 1).val])
 rw [h0,h1]
 simp [stream,unary,List.reverse_append,List.reverse_cons,List.append_assoc]
/-- Actual tail projection removes the four coordinate fields and retains the modulus. -/
def drop:=TailProjection.machine 3 (fun _=>false)
/-- The all-false four-field mask selects no coordinate. -/
theorem selected_none (i:ℕ) (xs:List ℕ):fields 3 (fun _=>false) i xs=[]:=by
 induction xs generalizing i with
 | nil=>rfl
 | cons b xs ih=>simp [fields,maskAt,ih]
/-- Counted clean run extracts its own modulus delimiter and unary value. -/
noncomputable def dropExec (a:Input):
 EvalsToInTime (TM2.step drop.program) (drop.init (input a)) (some (drop.halt (false::unary a.1.val)))
  (TailProjection.time.eval (input a).length):=by
 have h:=TailProjection.polyExec 3 (fun _=>false) (coords a.1.val a.2).reverse
  (by simp [coords,LPSMatrixProductMachine.fields]) (unary a.1.val)
 rw [selected_none] at h
 simp only [raw,stream,List.dropLast_nil,List.nil_append] at h
 rw [input_eq]
 exact h
/-- The merged actual q-only original LAST-occurrence PSL-list program. -/
def psl:=LPSOriginalPSLListMachine.machine
/-- Consume the actual delimiter before running the q-only PSL program. -/
def pslSwitch:=BooleanSwitch.machine psl psl
/-- Polynomial cost of delimiter consumption and original PSL generation. -/
noncomputable def pslSwitchTime:Polynomial ℕ:=LPSOriginalPSLListMachine.time+Polynomial.C 2
/-- The PSL program has distinct input and output channels. -/
theorem psl_io:psl.input≠psl.output:=by simp [psl,LPSOriginalPSLListMachine.machine,Composition.machine]
/-- Counted actual delimiter branch and original PSL-list output. -/
noncomputable def pslSwitchExec (a:Input):
 EvalsToInTime (TM2.step pslSwitch.program) (pslSwitch.init (false::unary a.1.val))
  (some (pslSwitch.halt (LPSOriginalPSLListMachine.output a.1.val)))
  (pslSwitchTime.eval (false::unary a.1.val).length):=by
 have hp:=LPSOriginalPSLListMachine.exec a.1
 have h:=BooleanSwitch.execB psl psl psl_io psl_io _ _ _ hp
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hm:=Composition.polynomial_eval_monotone LPSOriginalPSLListMachine.time
  (show (unary a.1.val).length≤(false::unary a.1.val).length by simp)
 dsimp only at hm
 simp only [pslSwitchTime,Polynomial.eval_add,Polynomial.eval_C]
 exact Nat.add_le_add_right hm 2
/-- Compose actual coordinate removal and original PSL-list generation. -/
def rowsBody:=Composition.machine drop pslSwitch
/-- Composition polynomial for extracting q and generating its original rows. -/
noncomputable def rowsTime:Polynomial ℕ:=Composition.timePolynomial drop TailProjection.time pslSwitchTime
/-- Actual q+matrix input generates its own original raw PSL representative rows. -/
noncomputable def rowsExec (a:Input):
 EvalsToInTime (TM2.step rowsBody.program) (rowsBody.init (input a))
  (some (rowsBody.halt (LPSOriginalPSLListMachine.output a.1.val))) (rowsTime.eval (input a).length):=
 LPSOriginalPSLListMachine.Initializer.composeRuns drop pslSwitch _ _ _ TailProjection.time pslSwitchTime
  (dropExec a) (pslSwitchExec a)
/-- Original PSL coverage guarantees at least one four-coordinate representative. -/
theorem original_fields_nonempty (a:Input):
 (representatives a.1.val (lpsSLList a.1.val)).flatMap (coords a.1.val)≠[]:=by
 have hm:(1:PSL(2,ZMod a.1.val))∈(representatives a.1.val (lpsSLList a.1.val)).map (quotient a.1.val):=by
  rw [mapped_original_representatives]
  exact mem_lpsPSLList a.1.val 1
 obtain ⟨A,hA,_⟩:=List.mem_map.mp hm
 intro he
 have hh:∀B∈representatives a.1.val (lpsSLList a.1.val),coords a.1.val B=[]:=List.flatMap_eq_nil_iff.mp he
 have hz:=hh A hA
 simp [coords,LPSMatrixProductMachine.fields] at hz
/-- Appending a real separator converts original raw fields into a forward stream. -/
theorem marked_source (a:Input):LPSOriginalPSLListMachine.output a.1.val++[false]=
 rows a.1.val (representatives a.1.val (lpsSLList a.1.val)):=by
 change raw ((representatives a.1.val (lpsSLList a.1.val)).flatMap (coords a.1.val))++[false]=_
 rw [MatrixListQuery.delimiter_raw _ (original_fields_nonempty a)]
 rfl
/-- Actual delimiter marking and reversal prepare rows for header restoration. -/
def reverseRows:=Composition.machine rowsBody LPSOriginalPSLListMachine.Initializer.markReverse
/-- Composition polynomial for original rows with marking and reversal. -/
noncomputable def reverseRowsTime:Polynomial ℕ:=Composition.timePolynomial rowsBody rowsTime LPSOriginalPSLListMachine.Initializer.markReverseTime
/-- Counted actual reversed original row stream. -/
noncomputable def reverseRowsExec (a:Input):
 EvalsToInTime (TM2.step reverseRows.program) (reverseRows.init (input a))
  (some (reverseRows.halt (rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse))
  (reverseRowsTime.eval (input a).length):=by
 have hm:=LPSOriginalPSLListMachine.Initializer.markReverseExec (LPSOriginalPSLListMachine.output a.1.val)
 rw [marked_source] at hm
 exact LPSOriginalPSLListMachine.Initializer.composeRuns rowsBody LPSOriginalPSLListMachine.Initializer.markReverse _ _ _
  rowsTime LPSOriginalPSLListMachine.Initializer.markReverseTime (rowsExec a) hm
/-- Consume the initializer-generated leading flag before row generation. -/
def switch:=BooleanSwitch.machine reverseRows reverseRows
/-- Polynomial for the actual leading-flag branch and row preparation. -/
noncomputable def switchTime:Polynomial ℕ:=reverseRowsTime+Polynomial.C 2
/-- Actual leading-flag branch generates the reversed original rows. -/
noncomputable def switchExec (a:Input):
 EvalsToInTime (TM2.step switch.program) (switch.init (false::input a))
  (some (switch.halt (rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse))
  (switchTime.eval (false::input a).length):=by
 have h:=BooleanSwitch.execB reverseRows reverseRows (by simp [reverseRows,Composition.machine])
  (by simp [reverseRows,Composition.machine]) _ _ _ (reverseRowsExec a)
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hm:=Composition.polynomial_eval_monotone reverseRowsTime
  (show (input a).length≤(false::input a).length by simp)
 dsimp only at hm
 simp only [switchTime,Polynomial.eval_add,Polynomial.eval_C]
 exact Nat.add_le_add_right hm 2
/-- Actual input-retention compiler preserves the original five-field query. -/
def retain:=RetainedInput.machine switch
/-- Polynomial counting query retention and original row generation. -/
noncomputable def retainTime:Polynomial ℕ:=RetainedInput.timePolynomial switch switchTime
/-- Counted actual retained query plus reversed original rows. -/
noncomputable def retainExec (a:Input):
 EvalsToInTime (TM2.step retain.program) (retain.init (false::input a))
  (some (retain.halt ((rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse++false::input a)))
  (retainTime.eval (false::input a).length):=
 RetainedInput.executes_polynomial switch (fun a:Input=>false::input a)
  (fun a=>(rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse) switchTime switchExec a
/-- Actual final reversal restores the forward query header and source row order. -/
def restore:=Composition.machine retain BitReverse.machine
/-- Composition polynomial for retaining and restoring the query. -/
noncomputable def restoreTime:Polynomial ℕ:=Composition.timePolynomial retain retainTime (Polynomial.X+1)
/-- Actual complete forward search input contains its own original PSL rows. -/
noncomputable def restoreExec (a:Input):
 EvalsToInTime (TM2.step restore.program) (restore.init (false::input a))
  (some (restore.halt (LPSPSLSearchMachine.input a.1.val a.2 (representatives a.1.val (lpsSLList a.1.val)))))
  (restoreTime.eval (false::input a).length):=by
 have hr:=BitReverse.exec ((rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse++false::input a)
 have he:((rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse++false::input a).reverse=
   LPSPSLSearchMachine.input a.1.val a.2 (representatives a.1.val (lpsSLList a.1.val)):=by
  calc
   _=raw (header a.1.val a.2)++[false]++rows a.1.val (representatives a.1.val (lpsSLList a.1.val)):=by
    simp [List.reverse_append,List.reverse_cons,input_reverse,List.append_assoc]
   _=_:=by
    rw [MatrixListQuery.delimiter_raw _ (by simp [header])]
    rfl
 rw [he] at hr
 exact LPSOriginalPSLListMachine.Initializer.composeRuns retain BitReverse.machine _ _ _ retainTime (Polynomial.X+1)
  (retainExec a) (by simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using hr)
/-- Actual false-prefix initialization composed with query retention and restoration. -/
def machine:=Composition.machine (FixedLiteral.prefixMachine [false]) restore
/-- Polynomial for every actual initializer stage. -/
noncomputable def time:Polynomial ℕ:=Composition.timePolynomial (FixedLiteral.prefixMachine [false]) (FixedLiteral.prefixTime [false]) restoreTime
/-- Counted clean initializer run from only q and matrix to the complete source search input. -/
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
  (some (machine.halt (LPSPSLSearchMachine.input a.1.val a.2 (representatives a.1.val (lpsSLList a.1.val)))))
  (time.eval (input a).length):=
 LPSOriginalPSLListMachine.Initializer.composeRuns (FixedLiteral.prefixMachine [false]) restore _ _ _
  (FixedLiteral.prefixTime [false]) restoreTime (FixedLiteral.prefixExec [false] (input a)) (restoreExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine.Initializer

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Legal q+matrix-only domain of the complete original PSL index computation. -/
abbrev Input:=Initializer.Input
/-- Faithful canonical five-field input to the actual whole program. -/
def input (a:Input):List Bool:=Initializer.input a
/-- Unary value of the exact original PSL enumeration inverse on the matrix quotient. -/
def output (a:Input):List Bool:=unary (((lpsPSLEnumerationEquiv a.1.val).symm (quotient a.1.val a.2)).val)
/-- Actual original-row initializer composed with the actual counted PSL search. -/
def machine:=Composition.machine Initializer.machine indexedMachine
/-- Whole composition polynomial counting initialization and index search. -/
noncomputable def time:Polynomial ℕ:=Composition.timePolynomial Initializer.machine Initializer.time indexedTime
/-- Actual whole q+matrix-only execution returns the exact original enumeration index. -/
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
  (some (machine.halt (output a))) (time.eval (input a).length):=by
 have hi:=Initializer.exec a
 have hc:=indexedExec a.1.val a.2 (representatives a.1.val (lpsSLList a.1.val))
 rw [original_source_index] at hc
 exact LPSOriginalPSLListMachine.Initializer.composeRuns Initializer.machine indexedMachine _ _ _ Initializer.time indexedTime hi hc
/-- Standard Mathlib certificate for the complete q+matrix-only index program. -/
noncomputable def outputsInTime (a:Input):
 TM2OutputsInTime machine.toFinTM2 (input a) (some (output a)) (time.eval (input a).length):=
 Machine.outputsInTime machine _ _ _ (exec a)
/-- One fixed finite machine and polynomial compute every legal original PSL index. -/
noncomputable def computableInPolyTime:TM2ComputableInPolyTime input id output where
 tm:=machine.toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time
 outputsFun:=fun a=>by
  change TM2OutputsInTime machine.toFinTM2 (List.map id (input a)) (some (List.map id (output a))) (time.eval (input a).length)
  have h:=outputsInTime a
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
/-- Original unary index length is strictly below the genuine PSL carrier size. -/
theorem output_length_lt_card (a:Input):(output a).length<Fintype.card PSL(2,ZMod a.1.val):=by
 have h:=original_source_index_lt a.1.val a.2
 have hl:=congrArg List.length (mapped_original_representatives a.1.val)
 simp only [List.length_map] at hl
 have hc:(lpsPSLList a.1.val).length=Fintype.card PSL(2,ZMod a.1.val):=by
  simpa only [Fintype.card_fin] using Fintype.card_congr (lpsPSLEnumerationEquiv a.1.val)
 rw [hl,hc,original_source_index] at h
 simpa only [output,unary_length] using h
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Five canonical unary fields faithfully distinguish prime and SL matrix. -/
theorem input_injective:Function.Injective input:=by
 intro a b hab
 change raw ((coords a.1.val a.2).reverse++[a.1.val])=raw ((coords b.1.val b.2).reverse++[b.1.val]) at hab
 have he:stream ((coords a.1.val a.2).reverse++[a.1.val])=stream ((coords b.1.val b.2).reverse++[b.1.val]):=by
  rw [←MatrixListQuery.delimiter_raw _ (by simp),←MatrixListQuery.delimiter_raw _ (by simp)]
  exact congrArg (fun w=>w++[false]) hab
 have hh:=stream_injective he
 rcases a with ⟨⟨q,hq⟩,A⟩
 rcases b with ⟨⟨r,hr⟩,B⟩
 simp only [coords,LPSMatrixProductMachine.fields,List.reverse_cons,List.reverse_nil,
  List.nil_append,List.cons_append,List.cons.injEq] at hh
 rcases hh with ⟨hd,hc,hb,ha,hqr,_⟩
 subst r
 have hAB:A=B:=by
  apply Subtype.ext
  apply LPSMatrixProductMachine.fields_injective q hq.pos
  simp [LPSMatrixProductMachine.fields,ha,hb,hc,hd]
 subst B
 rfl
/-- Canonical coordinate values bound the legal input size by 5q+4. -/
theorem input_length_le (a:Input):(input a).length≤ 5*a.1.val+4:=by
 let:NeZero a.1.val:=⟨a.1.property.ne_zero⟩
 have h00:=ZMod.val_lt (a.2.val 0 0)
 have h01:=ZMod.val_lt (a.2.val 0 1)
 have h10:=ZMod.val_lt (a.2.val 1 0)
 have h11:=ZMod.val_lt (a.2.val 1 1)
 simp only [input,Initializer.input_eq,List.length_append,stream_length,List.sum_reverse,List.length_reverse,
  coords,LPSMatrixProductMachine.fields,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,unary_length]
 omega
/-- Whole time polynomial after substituting the genuine PSL carrier input bound. -/
noncomputable def blockTime:Polynomial ℕ:=time.comp (Polynomial.C 10*Polynomial.X+Polynomial.C 4)
/-- Actual whole index execution timed in the original residue-prime PSL carrier. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (A:SL(2,ZMod a.q)):
 EvalsToInTime (TM2.step machine.program) (machine.init (input ⟨⟨a.q,a.prime⟩,A⟩))
  (some (machine.halt (output ⟨⟨a.q,a.prime⟩,A⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨⟨a.q,a.prime⟩,A⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hL:(input ⟨⟨a.q,a.prime⟩,A⟩).length≤ 10*Fintype.card PSL(2,ZMod a.q)+4:=by
  have hh:=input_length_le ⟨⟨a.q,a.prime⟩,A⟩
  have hq:=a.q_le_two_mul_card_psl
  dsimp only at hh
  omega
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time hL
/-- Standard actual whole output certificate in the genuine carrier budget. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (A:SL(2,ZMod a.q)):
 TM2OutputsInTime machine.toFinTM2 (input ⟨⟨a.q,a.prime⟩,A⟩) (some (output ⟨⟨a.q,a.prime⟩,A⟩))
  (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a A)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLIndexMachine
