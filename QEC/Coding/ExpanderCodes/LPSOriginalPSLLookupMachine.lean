import QEC.Coding.BitTuring.UnaryFourFieldLookup
import QEC.Coding.ExpanderCodes.LPSOriginalPSLIndexMachine

/-!
# Actual original PSL index-to-matrix lookup

One fixed finite tape program takes only prime q and its original finite PSL index.
It generates its own original LAST-occurrence representative list, retains/restores
the query and physically selects the indexed record. Whole counted execution,
faithful two-field input, source quotient and index roundtrips, standard polynomial
computation and timing in the genuine PSL carrier size are proved. Full sparse CSS
execution and unconditional strong centered-theta growth remain PK22 obligations.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.Initializer
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩

/-- Only prime q and its original finite PSL index enter initialization. -/
abbrev Input:=Σa:LPSOriginalPSLListMachine.Initializer.Input,Fin (lpsPSLList a.val).length
instance (a:Input):Fact a.1.val.Prime:=⟨a.1.property⟩

/-- Faithful two-field encoding stores the original index before the modulus. -/
def input (a:Input):List Bool:=raw [a.2.val,a.1.val]

/-- Separate the actual index field from the unary modulus. -/
theorem input_eq (a:Input):input a=stream [a.2.val]++unary a.1.val:=by
 simpa only [input,List.cons_append,List.nil_append] using raw_append_last [a.2.val] a.1.val

/-- Actual bit reversal restores the modulus and finite original index fields. -/
theorem input_reverse (a:Input):(input a).reverse=raw [a.1.val,a.2.val]:=by
 simp [input,show raw [a.2.val,a.1.val]=unary a.2.val++false::unary a.1.val by simpa [stream] using raw_append_last [a.2.val] a.1.val,
  show raw [a.1.val,a.2.val]=unary a.1.val++false::unary a.2.val by simpa [stream] using raw_append_last [a.1.val] a.2.val,
  List.reverse_append,List.reverse_cons,unary,List.append_assoc]

/-- Actual tail projection removes only the index field and retains its own modulus. -/
def drop:=TailProjection.machine 0 (fun _=>false)

/-- The all-false one-field mask selects no index payload. -/
theorem selected_none (i:ℕ) (xs:List ℕ):fields 0 (fun _=>false) i xs=[]:=by
 induction xs generalizing i with
 | nil=>rfl
 | cons b xs ih=>simp [fields,maskAt,ih]

/-- Counted clean run extracts its own modulus delimiter and unary value. -/
noncomputable def dropExec (a:Input):
 EvalsToInTime (TM2.step drop.program) (drop.init (input a)) (some (drop.halt (false::unary a.1.val)))
  (TailProjection.time.eval (input a).length):=by
 have h:=TailProjection.polyExec 0 (fun _=>false) [a.2.val]
  (by rfl) (unary a.1.val)
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

/-- Compose actual index-field removal and original PSL-list generation. -/
def rowsBody:=Composition.machine drop pslSwitch

/-- Composition polynomial for extracting q and generating its original rows. -/
noncomputable def rowsTime:Polynomial ℕ:=Composition.timePolynomial drop TailProjection.time pslSwitchTime

/-- The q+index input generates its own original raw PSL representative rows. -/
noncomputable def rowsExec (a:Input):
 EvalsToInTime (TM2.step rowsBody.program) (rowsBody.init (input a))
  (some (rowsBody.halt (LPSOriginalPSLListMachine.output a.1.val))) (rowsTime.eval (input a).length):=
 LPSOriginalPSLListMachine.Initializer.composeRuns drop pslSwitch _ _ _ TailProjection.time pslSwitchTime
  (dropExec a) (pslSwitchExec a)

/-- Original PSL coverage guarantees at least one four-coordinate representative. -/
theorem original_fields_nonempty (a:Input):
 (representatives a.1.val (lpsSLList a.1.val)).flatMap (coords a.1.val)≠[]:=
 LPSOriginalPSLIndexMachine.Initializer.original_fields_nonempty ⟨a.1,1⟩

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

/-- Actual input-retention compiler preserves the original two-field query. -/
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

/-- Actual complete forward lookup input contains its own original PSL rows. -/
noncomputable def restoreExec (a:Input):
 EvalsToInTime (TM2.step restore.program) (restore.init (false::input a))
  (some (restore.halt (QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.input a.1.val a.2.val ((representatives a.1.val (lpsSLList a.1.val)).map (coords a.1.val)))))
  (restoreTime.eval (false::input a).length):=by
 have hr:=BitReverse.exec ((rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse++false::input a)
 have he:((rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse++false::input a).reverse=
   QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.input a.1.val a.2.val ((representatives a.1.val (lpsSLList a.1.val)).map (coords a.1.val)):=by
  calc
   _=raw [a.1.val,a.2.val]++[false]++rows a.1.val (representatives a.1.val (lpsSLList a.1.val)):=by
    simp [List.reverse_append,List.reverse_cons,input_reverse,List.append_assoc]
   _=_:=by
    rw [MatrixListQuery.delimiter_raw _ (by simp)]
    simp only [QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.input,QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.rows,rows]
    rfl
 rw [he] at hr
 exact LPSOriginalPSLListMachine.Initializer.composeRuns retain BitReverse.machine _ _ _ retainTime (Polynomial.X+1)
  (retainExec a) (by simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using hr)

/-- Actual false-prefix initialization composed with query retention and restoration. -/
def machine:=Composition.machine (FixedLiteral.prefixMachine [false]) restore

/-- Polynomial for every actual initializer stage. -/
noncomputable def time:Polynomial ℕ:=Composition.timePolynomial (FixedLiteral.prefixMachine [false]) (FixedLiteral.prefixTime [false]) restoreTime

/-- Counted clean initializer from q and index to its own original ordered lookup stream. -/
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
  (some (machine.halt (QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.input a.1.val a.2.val ((representatives a.1.val (lpsSLList a.1.val)).map (coords a.1.val)))))
  (time.eval (input a).length):=
 LPSOriginalPSLListMachine.Initializer.composeRuns (FixedLiteral.prefixMachine [false]) restore _ _ _
  (FixedLiteral.prefixTime [false]) restoreTime (FixedLiteral.prefixExec [false] (input a)) (restoreExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.Initializer
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- The original source LAST-occurrence representative list, in unchanged order. -/
def originalReps (q:ℕ) [Fact q.Prime]:List SL(2,ZMod q):=representatives q (lpsSLList q)
/-- Original representative count equals the exact quotient enumeration length. -/
theorem original_length (q:ℕ) [Fact q.Prime]:(originalReps q).length=(lpsPSLList q).length:=by
 simpa only [List.length_map,originalReps] using congrArg List.length (mapped_original_representatives q)
/-- Select the source retained matrix at the original finite enumeration position. -/
def representative (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):SL(2,ZMod q):=
 (originalReps q)[i.val]'(by rw [original_length];exact i.isLt)
/-- The selected original representative quotient is exactly the source enumeration value. -/
theorem representative_decode (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 quotient q (representative q i)=(lpsPSLEnumerationEquiv q) i:=by
 have h:((originalReps q).map (quotient q))[i.val]'(by simp only [List.length_map,original_length];exact i.isLt)=
   (lpsPSLList q)[i.val]:=by simp only [show (originalReps q).map (quotient q)=lpsPSLList q from mapped_original_representatives q]
 change quotient q ((originalReps q)[i.val]'(by rw [original_length];exact i.isLt)) = (lpsPSLList q)[i.val]
 simpa only [List.getElem_map] using h
/-- The merged original index function returns the supplied finite position. -/
theorem original_index_roundtrip (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 LPSOriginalPSLIndexMachine.rowIndex q (representative q i) (originalReps q)=i.val:=by
 rw [originalReps,LPSOriginalPSLIndexMachine.original_source_index,representative_decode,Equiv.symm_apply_apply]
/-- Lookup after original quotient indexing recovers that exact quotient. -/
theorem original_lookup_quotient_roundtrip (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)):
 quotient q (representative q ((lpsPSLEnumerationEquiv q).symm (quotient q A)))=quotient q A:=by
 rw [representative_decode,Equiv.apply_symm_apply]
/-- Legal q+index-only domain of the complete source lookup computation. -/
abbrev Input:=Initializer.Input
instance (a:Input):Fact a.1.val.Prime:=⟨a.1.property⟩
/-- Faithful canonical two-field input of the actual complete program. -/
def input (a:Input):List Bool:=Initializer.input a
/-- Four canonical coordinates of the original retained source matrix. -/
def output (a:Input):List Bool:=raw (coords a.1.val (representative a.1.val a.2))
/-- Actual own-source-list initializer composed with actual ordered row lookup and reversal. -/
def machine:=Composition.machine Initializer.machine FourFieldLookup.forwardMachine
/-- Whole polynomial counting initialization, row traversal, cleanup and output restoration. -/
noncomputable def time:Polynomial ℕ:=Composition.timePolynomial Initializer.machine Initializer.time FourFieldLookup.forwardTime
/-- Actual complete q+index-only execution returns the exact original source matrix fields. -/
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
 (some (machine.halt (output a))) (time.eval (input a).length):=by
 have hi:a.2.val<((originalReps a.1.val).map (coords a.1.val)).length:=by
  simp only [List.length_map,original_length];exact a.2.isLt
 have hr:∀r∈(originalReps a.1.val).map (coords a.1.val),r.length=4:=by
  intro r hh
  obtain ⟨A,_,rfl⟩:=List.mem_map.mp hh
  simp [coords,LPSMatrixProductMachine.fields]
 have h:=FourFieldLookup.forwardExec a.1.val a.2.val ((originalReps a.1.val).map (coords a.1.val)) hi hr
 simp only [List.getElem_map] at h
 exact LPSOriginalPSLListMachine.Initializer.composeRuns Initializer.machine FourFieldLookup.forwardMachine _ _ _
  Initializer.time FourFieldLookup.forwardTime (Initializer.exec a) h
/-- Standard Mathlib output certificate for the whole original lookup. -/
noncomputable def outputsInTime (a:Input):
 TM2OutputsInTime machine.toFinTM2 (input a) (some (output a)) (time.eval (input a).length):=
 Machine.outputsInTime machine _ _ _ (exec a)
/-- One fixed finite machine and polynomial compute every legal original PSL lookup. -/
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
/-- The two unary fields faithfully distinguish prime and original finite index. -/
theorem input_injective:Function.Injective input:=by
 intro a b hab
 change raw [a.2.val,a.1.val]=raw [b.2.val,b.1.val] at hab
 have he:stream [a.2.val,a.1.val]=stream [b.2.val,b.1.val]:=by
  rw [←MatrixListQuery.delimiter_raw _ (by simp),←MatrixListQuery.delimiter_raw _ (by simp)]
  exact congrArg (fun w=>w++[false]) hab
 have hh:=stream_injective he
 rcases a with ⟨⟨q,hq⟩,i⟩
 rcases b with ⟨⟨r,hr⟩,j⟩
 simp only [List.cons.injEq] at hh
 rcases hh with ⟨hij,hqr,_⟩
 subst r
 have hi:i=j:=Fin.ext hij
 subst j
 rfl
/-- Exact size of the two-field modulus/index input. -/
theorem input_length (a:Input):(input a).length=a.2.val+a.1.val+1:=by
 change (raw [a.2.val,a.1.val]).length=_
 rw [show raw [a.2.val,a.1.val]=stream [a.2.val]++unary a.1.val from raw_append_last [a.2.val] a.1.val]
 simp only [List.length_append,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,unary_length]
 omega
/-- Original finite index range has the genuine PSL carrier size. -/
theorem original_length_card (q:ℕ) [Fact q.Prime]:(lpsPSLList q).length=Fintype.card PSL(2,ZMod q):=by
 simpa only [Fintype.card_fin] using Fintype.card_congr (lpsPSLEnumerationEquiv q)
/-- Finite original index bounds actual input length by carrier size plus modulus. -/
theorem input_length_lt_card (a:Input):(input a).length<Fintype.card PSL(2,ZMod a.1.val)+a.1.val+1:=by
 rw [input_length]
 have h:a.2.val<Fintype.card PSL(2,ZMod a.1.val):=a.2.isLt.trans_le (le_of_eq (original_length_card a.1.val))
 omega
/-- Four bounded canonical coordinates bound actual output length. -/
theorem output_length_le (a:Input):(output a).length≤4*a.1.val+3:=by
 let:NeZero a.1.val:=⟨a.1.property.ne_zero⟩
 let A:=representative a.1.val a.2
 have h00:=ZMod.val_lt (A.val 0 0)
 have h01:=ZMod.val_lt (A.val 0 1)
 have h10:=ZMod.val_lt (A.val 1 0)
 have h11:=ZMod.val_lt (A.val 1 1)
 have hh:=raw_length_le (coords a.1.val A)
 simp only [stream_length,coords,LPSMatrixProductMachine.fields,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hh
 change (raw (coords a.1.val A)).length≤_
 simp only [coords,LPSMatrixProductMachine.fields]
 omega
/-- Whole time polynomial after genuine residue-prime carrier substitution. -/
noncomputable def blockTime:Polynomial ℕ:=time.comp (Polynomial.C 3*Polynomial.X+Polynomial.C 1)
/-- Actual clean whole lookup with time measured in the genuine PSL carrier size. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (i:Fin (lpsPSLList a.q).length):
 EvalsToInTime (TM2.step machine.program) (machine.init (input ⟨⟨a.q,a.prime⟩,i⟩))
 (some (machine.halt (output ⟨⟨a.q,a.prime⟩,i⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨⟨a.q,a.prime⟩,i⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hL:(input ⟨⟨a.q,a.prime⟩,i⟩).length≤3*Fintype.card PSL(2,ZMod a.q)+1:=by
  have hh:=input_length_lt_card ⟨⟨a.q,a.prime⟩,i⟩
  have hq:=a.q_le_two_mul_card_psl
  dsimp only at hh
  omega
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time hL
/-- Standard whole output certificate within that genuine carrier budget. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (i:Fin (lpsPSLList a.q).length):
 TM2OutputsInTime machine.toFinTM2 (input ⟨⟨a.q,a.prime⟩,i⟩) (some (output ⟨⟨a.q,a.prime⟩,i⟩))
 (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a i)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine
