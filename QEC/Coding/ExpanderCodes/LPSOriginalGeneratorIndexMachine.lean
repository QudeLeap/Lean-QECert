import QEC.Coding.BitTuring.UnaryRetainedFieldComputation
import QEC.Coding.ExpanderCodes.LPSOriginalPSLIndexMachine
import QEC.Coding.ExpanderCodes.LPSOriginalPSLLookupMachine
import QEC.Coding.ExpanderCodes.LPSGeneratorMatrixListMachine
import QEC.Coding.ExpanderCodes.LPSEffectivePrime

/-!
# Actual q-only original LPS generator and identity indices

Fixed quaternion directions determine the finite programs; only unary graph prime q enters
execution. The programs compute the original effective normalized SL matrices, physically
prepare original matrix-to-index queries and execute the original own-list index search.
An actual tail-first retained collector preserves the exact original direction order. The
identity program writes only the fixed identity matrix header, then runs original indexing.
Complete clean execution, faithful input, standard Mathlib certificates and true PSL-carrier
polynomials are proved. Neither matrices, roots, lists nor answer indices are caller inputs.

Original source directions use the existing Jacobi-based equivalence, without replacement
numbering or permutation. These internal runtime theorems support the sparse CSS construction;
the complete sparse emitter and unconditional strong centered-theta estimate remain needed
for the source-backed public asymptotically good qLDPC theorem.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Exact original effective normalized SL matrix, used only as the output specification. -/
def matrix {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):SL(2,ZMod a.q):=
 LPSGeneratorMatrixListMachine.generatorSL a t
/-- Original source quaternion vertex index in the unchanged LAST quotient enumeration. -/
def result {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):Fin (lpsPSLList a.q).length:=
 lpsQuaternionVertexIndex a t.val (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.property)
/-- Fixed finite program for selected actual q-only computation while retaining the complete earlier stream. -/
def query {p:ℕ} (t:LPSGeneratorIndex p):=RetainedFieldComputation.machine 0 (ModulusQuery.mask 0) (LPSQuaternionMatrixMachine.machine p t.val)
/-- Polynomial counting selected actual q-only computation while retaining the complete earlier stream. -/
noncomputable def queryTime {p:ℕ} (t:LPSGeneratorIndex p):=RetainedFieldComputation.time 0 (ModulusQuery.mask 0) (LPSQuaternionMatrixMachine.machine p t.val) (LPSQuaternionMatrixMachine.time p t.val)
/-- Prove complete clean execution of selected actual q-only computation while retaining the complete earlier stream. -/
noncomputable def queryExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step (query t).program) ((query t).init (stream [a.q]))
 (some ((query t).halt (stream (coords a.q (matrix a t)++[a.q])))) ((queryTime t).eval (stream [a.q]).length):=by
 have hf:fields 0 (ModulusQuery.mask 0) 0 [a.q]=[a.q]:=by simp [fields,maskAt,ModulusQuery.mask]
 have he:raw [a.q]=unary a.q:=by simpa [stream] using raw_append_last [] a.q
 have hb:EvalsToInTime (TM2.step (LPSQuaternionMatrixMachine.machine p t.val).program)
  ((LPSQuaternionMatrixMachine.machine p t.val).init (raw (fields 0 (ModulusQuery.mask 0) 0 [a.q])))
  (some ((LPSQuaternionMatrixMachine.machine p t.val).halt (raw (coords a.q (matrix a t)))))
  ((LPSQuaternionMatrixMachine.time p t.val).eval (raw (fields 0 (ModulusQuery.mask 0) 0 [a.q])).length):=by
  rw [hf,he]
  exact LPSQuaternionMatrixMachine.polyExec a t.val (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.property)
 have h:=RetainedFieldComputation.exec 0 (ModulusQuery.mask 0) (LPSQuaternionMatrixMachine.machine p t.val)
  [a.q] (coords a.q (matrix a t)) (by rfl) (by simp [coords,LPSMatrixProductMachine.fields]) (LPSQuaternionMatrixMachine.time p t.val) hb
 rw [←MatrixListQuery.stream_append] at h
 exact h
/-- Fixed finite program for copying the retained final q to the front of computed matrix coordinates. -/
def retainModulus:=ModularAdjugate.retainedUnary 4 (ModulusQuery.mask 4)
/-- Prove complete clean execution of copying the retained final q to the front of computed matrix coordinates. -/
noncomputable def retainModulusExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step retainModulus.program) (retainModulus.init (stream (coords a.q (matrix a t)++[a.q])))
 (some (retainModulus.halt (stream (a.q::coords a.q (matrix a t)++[a.q]))))
 (ModularAdjugate.stageTime.eval (stream (coords a.q (matrix a t)++[a.q])).length):=
 ModularAdjugate.unaryStageExec 4 (ModulusQuery.mask 4) _
  (by simp [coords,LPSMatrixProductMachine.fields]) a.q
  (MatrixListQuery.selectLast 4 0 (coords a.q (matrix a t)) a.q (by simp [coords,LPSMatrixProductMachine.fields]))
/-- Fixed mask retains front modulus and four newly computed matrix coordinates. -/
def firstFive (k:Fin 6):Bool:=decide (k.val<5)
/-- The fixed mask selects exactly q followed by the computed matrix fields. -/
theorem first_five_fields {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 fields 5 firstFive 0 (a.q::coords a.q (matrix a t)++[a.q])=a.q::coords a.q (matrix a t):=by
 simp [coords,LPSMatrixProductMachine.fields,fields,maskAt,firstFive]
/-- Fixed finite program for selecting the first five fields and reversing their bits for original indexing. -/
def prepareIndex:=RetainedFieldComputation.projectedReverse 5 firstFive
/-- Polynomial counting selecting the first five fields and reversing their bits for original indexing. -/
noncomputable def prepareIndexTime:=RetainedFieldComputation.projectedReverseTime 5 firstFive
/-- Prove complete clean execution of selecting the first five fields and reversing their bits for original indexing. -/
noncomputable def prepareIndexExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step prepareIndex.program) (prepareIndex.init (stream (a.q::coords a.q (matrix a t)++[a.q])))
 (some (prepareIndex.halt (LPSOriginalPSLIndexMachine.input ⟨⟨a.q,a.prime⟩,matrix a t⟩)))
 (prepareIndexTime.eval (stream (a.q::coords a.q (matrix a t)++[a.q])).length):=by
 have h:=RetainedFieldComputation.projectedReverseExec 5 firstFive (a.q::coords a.q (matrix a t)++[a.q])
  (by simp [coords,LPSMatrixProductMachine.fields])
 rw [first_five_fields] at h
 have he:(raw (a.q::coords a.q (matrix a t))).reverse=LPSOriginalPSLIndexMachine.input ⟨⟨a.q,a.prime⟩,matrix a t⟩:=by
  have hi:=LPSOriginalPSLIndexMachine.Initializer.input_reverse ⟨⟨a.q,a.prime⟩,matrix a t⟩
  change (LPSOriginalPSLIndexMachine.Initializer.input ⟨⟨a.q,a.prime⟩,matrix a t⟩).reverse=raw (a.q::coords a.q (matrix a t)) at hi
  rw [←hi,List.reverse_reverse]
  rfl
 rw [he] at h
 exact h
/-- Exact original index or ordered table Boolean output specification. -/
def output {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):List Bool:=unary (result a t).val
/-- Original quotient indexing agrees with the source generator or identity index. -/
theorem source_output {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 LPSOriginalPSLIndexMachine.output ⟨⟨a.q,a.prime⟩,matrix a t⟩=output a t:=by
 simp only [LPSOriginalPSLIndexMachine.output,output,result,matrix,LPSGeneratorMatrixListMachine.generatorSL,
  lpsQuaternionVertexIndex,lpsEffectiveQuaternionPSL,quotient]
/-- Fixed finite program for physical query preparation followed by actual original matrix-to-index search. -/
def indexed:=Composition.machine prepareIndex LPSOriginalPSLIndexMachine.machine
/-- Polynomial counting physical query preparation followed by actual original matrix-to-index search. -/
noncomputable def indexedTime:=Composition.timePolynomial prepareIndex prepareIndexTime LPSOriginalPSLIndexMachine.time
/-- Prove complete clean execution of physical query preparation followed by actual original matrix-to-index search. -/
noncomputable def indexedExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step indexed.program) (indexed.init (stream (a.q::coords a.q (matrix a t)++[a.q])))
 (some (indexed.halt (output a t))) (indexedTime.eval (stream (a.q::coords a.q (matrix a t)++[a.q])).length):=by
 have h:=LPSOriginalPSLIndexMachine.exec ⟨⟨a.q,a.prime⟩,matrix a t⟩
 rw [source_output] at h
 exact RetainedFieldComputation.composeRuns prepareIndex LPSOriginalPSLIndexMachine.machine _ _ _ prepareIndexTime LPSOriginalPSLIndexMachine.time (prepareIndexExec a t) h
/-- Fixed finite program for actual modulus copying followed by exact original source indexing. -/
def modulusAndIndex:=Composition.machine retainModulus indexed
/-- Polynomial counting actual modulus copying followed by exact original source indexing. -/
noncomputable def modulusAndIndexTime:=Composition.timePolynomial retainModulus ModularAdjugate.stageTime indexedTime
/-- Prove complete clean execution of actual modulus copying followed by exact original source indexing. -/
noncomputable def modulusAndIndexExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step modulusAndIndex.program) (modulusAndIndex.init (stream (coords a.q (matrix a t)++[a.q])))
 (some (modulusAndIndex.halt (output a t))) (modulusAndIndexTime.eval (stream (coords a.q (matrix a t)++[a.q])).length):=
 RetainedFieldComputation.composeRuns retainModulus indexed _ _ _ ModularAdjugate.stageTime indexedTime (retainModulusExec a t) (indexedExec a t)
/-- Fixed finite program for actual normalized quaternion matrix computation followed by original indexing. -/
def queryAndIndex {p:ℕ} (t:LPSGeneratorIndex p):=Composition.machine (query t) modulusAndIndex
/-- Polynomial counting actual normalized quaternion matrix computation followed by original indexing. -/
noncomputable def queryAndIndexTime {p:ℕ} (t:LPSGeneratorIndex p):=Composition.timePolynomial (query t) (queryTime t) modulusAndIndexTime
/-- Prove complete clean execution of actual normalized quaternion matrix computation followed by original indexing. -/
noncomputable def queryAndIndexExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step (queryAndIndex t).program) ((queryAndIndex t).init (stream [a.q]))
 (some ((queryAndIndex t).halt (output a t))) ((queryAndIndexTime t).eval (stream [a.q]).length):=
 RetainedFieldComputation.composeRuns (query t) modulusAndIndex _ _ _ (queryTime t) modulusAndIndexTime (queryExec a t) (modulusAndIndexExec a t)
/-- Fixed finite program for the complete actual q-only original index or voltage-table program. -/
def machine {p:ℕ} (t:LPSGeneratorIndex p):=Composition.machine BitDelimiter.machine (queryAndIndex t)
/-- Polynomial counting the complete actual q-only original index or voltage-table program. -/
noncomputable def time {p:ℕ} (t:LPSGeneratorIndex p):=Composition.timePolynomial BitDelimiter.machine (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (queryAndIndexTime t)
/-- Prove complete clean execution of the complete actual q-only original index or voltage-table program. -/
noncomputable def exec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step (machine t).program) ((machine t).init (unary a.q))
 (some ((machine t).halt (output a t))) ((time t).eval (unary a.q).length):=by
 have h:=BitDelimiter.exec (unary a.q)
 have he:unary a.q++[false]=stream [a.q]:=by simp [stream]
 rw [he] at h
 exact RetainedFieldComputation.composeRuns BitDelimiter.machine (queryAndIndex t) _ _ _ (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (queryAndIndexTime t)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using h) (queryAndIndexExec a t)
/-- Standard Mathlib output certificate derived from complete actual clean execution. -/
noncomputable def outputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 TM2OutputsInTime (machine t).toFinTM2 (unary a.q) (some (output a t)) ((time t).eval (unary a.q).length):=
 Machine.outputsInTime (machine t) _ _ _ (exec a t)
/-- One fixed actual finite program computes all legal q-only outputs in polynomial time. -/
noncomputable def computableInPolyTime {p:ℕ} (t:LPSGeneratorIndex p):
 TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>output a t) where
 tm:=(machine t).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time t
 outputsFun:=fun a=>by
  change TM2OutputsInTime (machine t).toFinTM2 (List.map id (unary a.q)) (some (List.map id (output a t))) ((time t).eval (unary a.q).length)
  have h:=outputsInTime a t
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
/-- Unary prime input faithfully distinguishes every varying legal graph input. -/
theorem input_injective (p:ℕ):Function.Injective (fun a:LPSResiduePrime p=>unary a.q):=lpsResiduePrime_unary_injective p
/-- Original unary generator index length is below the genuine PSL cardinality. -/
theorem output_length_lt_card {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 (output a t).length<Fintype.card PSL(2,ZMod a.q):=by
 have h:(result a t).val<(lpsPSLList a.q).length:=(result a t).isLt
 have hh:=h.trans_le (LPSOriginalPSLLookupMachine.original_length_card a.q).le
 simpa only [output,unary_length] using hh
/-- Whole actual program polynomial after genuine PSL-carrier substitution. -/
noncomputable def blockTime {p:ℕ} (t:LPSGeneratorIndex p):Polynomial ℕ:=(time t).comp (Polynomial.C 2*Polynomial.X)
/-- Complete actual q-only output within the genuine PSL-carrier polynomial. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step (machine t).program) ((machine t).init (unary a.q))
 (some ((machine t).halt (output a t))) ((blockTime t).eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec a t
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone (time t) (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
/-- Standard actual output certificate at the genuine PSL-carrier budget. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 TM2OutputsInTime (machine t).toFinTM2 (unary a.q) (some (output a t)) ((blockTime t).eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime (machine t) _ _ _ (blockExec a t)
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Ordered specification of original generator index values, never input to the program. -/
def indices {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):List ℕ:=ts.map (fun t=>(result a t).val)
/-- One original finite index is emitted per fixed quaternion direction. -/
theorem indices_length {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):(indices a ts).length=ts.length:=by simp [indices]
/-- Fixed finite program for selected actual q-only computation while retaining the complete earlier stream. -/
def query {p:ℕ} (n:ℕ) (t:LPSGeneratorIndex p):=RetainedFieldComputation.machine n (ModulusQuery.mask n) (LPSOriginalGeneratorIndexMachine.machine t)
/-- Polynomial counting selected actual q-only computation while retaining the complete earlier stream. -/
noncomputable def queryTime {p:ℕ} (n:ℕ) (t:LPSGeneratorIndex p):=RetainedFieldComputation.time n (ModulusQuery.mask n) (LPSOriginalGeneratorIndexMachine.machine t) (LPSOriginalGeneratorIndexMachine.time t)
/-- Prove complete clean execution of selected actual q-only computation while retaining the complete earlier stream. -/
noncomputable def queryExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (query ts.length t).program) ((query ts.length t).init (stream (indices a ts++[a.q])))
 (some ((query ts.length t).halt (stream ((result a t).val::indices a ts++[a.q]))))
 ((queryTime ts.length t).eval (stream (indices a ts++[a.q])).length):=by
 have hf:=MatrixListQuery.selectLast ts.length 0 (indices a ts) a.q (by simp [indices_length])
 have he:raw [a.q]=unary a.q:=by simpa [stream] using raw_append_last [] a.q
 have hb:EvalsToInTime (TM2.step (LPSOriginalGeneratorIndexMachine.machine t).program)
  ((LPSOriginalGeneratorIndexMachine.machine t).init (raw (fields ts.length (ModulusQuery.mask ts.length) 0 (indices a ts++[a.q]))))
  (some ((LPSOriginalGeneratorIndexMachine.machine t).halt (raw [(result a t).val])))
  ((LPSOriginalGeneratorIndexMachine.time t).eval (raw (fields ts.length (ModulusQuery.mask ts.length) 0 (indices a ts++[a.q]))).length):=by
  rw [hf,he]
  have hr:raw [(result a t).val]=unary (result a t).val:=by simpa [stream] using raw_append_last [] (result a t).val
  rw [hr]
  exact LPSOriginalGeneratorIndexMachine.exec a t
 have h:=RetainedFieldComputation.exec ts.length (ModulusQuery.mask ts.length) (LPSOriginalGeneratorIndexMachine.machine t)
  (indices a ts++[a.q]) [(result a t).val] (by simp [indices_length]) (by simp) (LPSOriginalGeneratorIndexMachine.time t) hb
 have he:stream [(result a t).val]++stream (indices a ts++[a.q])=stream ((result a t).val::indices a ts++[a.q]):=by
  rw [←MatrixListQuery.stream_append]
  rfl
 rw [he] at h
 exact h
/-- Fixed finite program for actual tail-first ordered direction collection with the varying q retained. -/
def collector {p:ℕ}:List (LPSGeneratorIndex p)→Machine
 | []=>MatrixListQuery.identityMachine
 | t::ts=>Composition.machine (collector ts) (query ts.length t)
/-- Polynomial counting actual tail-first ordered direction collection with the varying q retained. -/
noncomputable def collectorTime {p:ℕ}:List (LPSGeneratorIndex p)→Polynomial ℕ
 | []=>Polynomial.C 4*Polynomial.X+Polynomial.C 4
 | t::ts=>Composition.timePolynomial (collector ts) (collectorTime ts) (queryTime ts.length t)
/-- Prove complete clean execution of actual tail-first ordered direction collection with the varying q retained. -/
noncomputable def collectorExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (collector ts).program) ((collector ts).init (stream [a.q]))
 (some ((collector ts).halt (stream (indices a ts++[a.q])))) ((collectorTime ts).eval (stream [a.q]).length):=by
 induction ts with
 | nil=>
  have h:=MatrixListQuery.identityExec (stream [a.q])
  have he:(collectorTime ([]:List (LPSGeneratorIndex p))).eval (stream [a.q]).length=4*(stream [a.q]).length+4:=by
   simp only [collectorTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  rw [he]
  exact h
 | cons t ts ih=>
  have h:=RetainedFieldComputation.composeRuns (collector ts) (query ts.length t) _ _ _ (collectorTime ts) (queryTime ts.length t) ih (queryExec a t ts)
  exact h
/-- Fixed finite program for actual fixed field projection discarding only the retained final modulus. -/
def projector {p:ℕ} (ts:List (LPSGeneratorIndex p)):=FieldProjection.machine ts.length (MatrixListQuery.prefixMask ts.length)
/-- Prove complete clean execution of actual fixed field projection discarding only the retained final modulus. -/
noncomputable def projectorExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (projector ts).program) ((projector ts).init (stream (indices a ts++[a.q])))
 (some ((projector ts).halt (raw (indices a ts)))) (FieldProjection.time.eval (stream (indices a ts++[a.q])).length):=by
 have h:=FieldProjection.polyExec ts.length (MatrixListQuery.prefixMask ts.length) (indices a ts++[a.q]) (by simp [indices_length])
 rw [MatrixListQuery.selectPrefix ts.length 0 (indices a ts) a.q (by simp [indices_length])] at h
 exact h
/-- Fixed finite program for actual complete retained collection followed by final raw-output projection. -/
def collected {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine (collector ts) (projector ts)
/-- Polynomial counting actual complete retained collection followed by final raw-output projection. -/
noncomputable def collectedTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial (collector ts) (collectorTime ts) FieldProjection.time
/-- Prove complete clean execution of actual complete retained collection followed by final raw-output projection. -/
noncomputable def collectedExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (collected ts).program) ((collected ts).init (stream [a.q]))
 (some ((collected ts).halt (raw (indices a ts)))) ((collectedTime ts).eval (stream [a.q]).length):=
 RetainedFieldComputation.composeRuns (collector ts) (projector ts) _ _ _ (collectorTime ts) FieldProjection.time (collectorExec a ts) (projectorExec a ts)
/-- Fixed finite program for the complete actual q-only original index or voltage-table program. -/
def machine {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine BitDelimiter.machine (collected ts)
/-- Polynomial counting the complete actual q-only original index or voltage-table program. -/
noncomputable def time {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial BitDelimiter.machine (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (collectedTime ts)
/-- Exact original index or ordered table Boolean output specification. -/
def output {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):List Bool:=raw (indices a ts)
/-- Prove complete clean execution of the complete actual q-only original index or voltage-table program. -/
noncomputable def exec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (machine ts).program) ((machine ts).init (unary a.q))
 (some ((machine ts).halt (output a ts))) ((time ts).eval (unary a.q).length):=by
 have h:=BitDelimiter.exec (unary a.q)
 have he:unary a.q++[false]=stream [a.q]:=by simp [stream]
 rw [he] at h
 exact RetainedFieldComputation.composeRuns BitDelimiter.machine (collected ts) _ _ _ (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (collectedTime ts)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using h) (collectedExec a ts)
/-- Standard Mathlib output certificate derived from complete actual clean execution. -/
noncomputable def outputsInTime {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 TM2OutputsInTime (machine ts).toFinTM2 (unary a.q) (some (output a ts)) ((time ts).eval (unary a.q).length):=
 Machine.outputsInTime (machine ts) _ _ _ (exec a ts)
/-- One fixed actual finite program computes all legal q-only outputs in polynomial time. -/
noncomputable def computableInPolyTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):
 TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>output a ts) where
 tm:=(machine ts).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time ts
 outputsFun:=fun a=>by
  change TM2OutputsInTime (machine ts).toFinTM2 (List.map id (unary a.q)) (some (List.map id (output a ts))) ((time ts).eval (unary a.q).length)
  have h:=outputsInTime a ts
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
/-- Whole actual program polynomial after genuine PSL-carrier substitution. -/
noncomputable def blockTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):Polynomial ℕ:=(time ts).comp (Polynomial.C 2*Polynomial.X)
/-- Complete actual q-only output within the genuine PSL-carrier polynomial. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (machine ts).program) ((machine ts).init (unary a.q))
 (some ((machine ts).halt (output a ts))) ((blockTime ts).eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec a ts
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone (time ts) (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
/-- Standard actual output certificate at the genuine PSL-carrier budget. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 TM2OutputsInTime (machine ts).toFinTM2 (unary a.q) (some (output a ts)) ((blockTime ts).eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime (machine ts) _ _ _ (blockExec a ts)
/-- Unary prime input faithfully distinguishes every varying legal graph input. -/
theorem input_injective (p:ℕ):Function.Injective (fun a:LPSResiduePrime p=>unary a.q):=LPSOriginalGeneratorIndexMachine.input_injective p
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Identity
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- The identity program legal input consists only of a varying prime. -/
abbrev Input:=LPSOriginalPSLListMachine.Initializer.Input
instance (a:Input):Fact a.val.Prime:=⟨a.property⟩
/-- Fixed identity matrix header; contains no varying prime or computed identity index. -/
def header:List Bool:=raw [1,0,0,1]++[false]
/-- Fixed finite program for actual fixed identity header writing while retaining the varying q. -/
def prepare:=FixedLiteral.prefixMachine header
/-- Polynomial counting actual fixed identity header writing while retaining the varying q. -/
noncomputable def prepareTime:=FixedLiteral.prefixTime header
/-- The fixed identity header and varying unary q are the exact original SL identity query. -/
theorem source_input (a:Input):header++unary a.val=LPSOriginalPSLIndexMachine.input ⟨a,1⟩:=by
 let:Fact (1<a.val):=⟨a.property.one_lt⟩
 have hh:=raw_append_last [1,0,0,1] a.val
 simp only [header] at hh ⊢
 rw [MatrixListQuery.delimiter_raw _ (by simp),←hh]
 simp [LPSOriginalPSLIndexMachine.input,LPSOriginalPSLIndexMachine.Initializer.input,
  coords,LPSMatrixProductMachine.fields,ZMod.val_one]
/-- Exact original index or ordered table Boolean output specification. -/
def output (a:Input):List Bool:=unary (lpsPSLIndexOne a.val).val
/-- Original quotient indexing agrees with the source generator or identity index. -/
theorem source_output (a:Input):LPSOriginalPSLIndexMachine.output ⟨a,1⟩=output a:=by
 simp [LPSOriginalPSLIndexMachine.output,output,lpsPSLIndexOne,quotient]
/-- Fixed finite program for the complete actual q-only original index or voltage-table program. -/
def machine:=Composition.machine prepare LPSOriginalPSLIndexMachine.machine
/-- Polynomial counting the complete actual q-only original index or voltage-table program. -/
noncomputable def time:=Composition.timePolynomial prepare prepareTime LPSOriginalPSLIndexMachine.time
/-- Prove complete clean execution of the complete actual q-only original index or voltage-table program. -/
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.val))
 (some (machine.halt (output a))) (time.eval (unary a.val).length):=by
 have hp:=FixedLiteral.prefixExec header (unary a.val)
 rw [source_input] at hp
 have hi:=LPSOriginalPSLIndexMachine.exec ⟨a,1⟩
 rw [source_output] at hi
 exact RetainedFieldComputation.composeRuns prepare LPSOriginalPSLIndexMachine.machine _ _ _ prepareTime LPSOriginalPSLIndexMachine.time hp hi
/-- Standard Mathlib output certificate derived from complete actual clean execution. -/
noncomputable def outputsInTime (a:Input):
 TM2OutputsInTime machine.toFinTM2 (unary a.val) (some (output a)) (time.eval (unary a.val).length):=
 Machine.outputsInTime machine _ _ _ (exec a)
/-- One fixed actual finite program computes all legal q-only outputs in polynomial time. -/
noncomputable def computableInPolyTime:TM2ComputableInPolyTime (fun a:Input=>unary a.val) id output where
 tm:=machine.toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time
 outputsFun:=fun a=>by
  change TM2OutputsInTime machine.toFinTM2 (List.map id (unary a.val)) (some (List.map id (output a))) (time.eval (unary a.val).length)
  have h:=outputsInTime a
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
/-- Unary prime input faithfully distinguishes every varying legal graph input. -/
theorem input_injective:Function.Injective (fun a:Input=>unary a.val):=by
 intro a b h
 apply Subtype.ext
 exact unary_injective h
/-- Whole actual program polynomial after genuine PSL-carrier substitution. -/
noncomputable def blockTime:Polynomial ℕ:=time.comp (Polynomial.C 2*Polynomial.X)
/-- Complete actual q-only output within the genuine PSL-carrier polynomial. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
 (some (machine.halt (output ⟨a.q,a.prime⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨a.q,a.prime⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
/-- Standard actual output certificate at the genuine PSL-carrier budget. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p):
 TM2OutputsInTime machine.toFinTM2 (unary a.q) (some (output ⟨a.q,a.prime⟩)) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Identity
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- The original finite index decodes to the exact original quaternion group label. -/
theorem result_decode {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 (lpsPSLEnumerationEquiv a.q) (result a t)=lpsQuaternionLabel a t:=
 lpsQuaternionVertexIndex_decode a t.val (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.property)
/-- Distinct original quaternion directions have distinct original finite vertex indices. -/
theorem result_injective {p:ℕ} (a:LPSResiduePrime p):Function.Injective (result a):=by
 intro t u h
 apply lpsQuaternionLabel_injective a
 have he:=congrArg (lpsPSLEnumerationEquiv a.q) h
 simpa only [result_decode] using he
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- The ordered collector specification preserves the given Fin direction ordering. -/
theorem ordered_indices {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p):
 indices a (List.ofFn g)=List.ofFn (fun j=>(result a (g j)).val):=by
 simp [indices,List.map_ofFn,Function.comp_def]
/-- Original generator-label injectivity preserves distinctness of the fixed direction list. -/
theorem indices_nodup {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) (h:ts.Nodup):
 (indices a ts).Nodup:=by
 apply h.map
 intro t u he
 apply result_injective a
 exact Fin.ext he
/-- Exact original source-ordered index output specification, independent of execution control. -/
noncomputable def sourceOutput {p:ℕ} (a:LPSResiduePrime p):List Bool:=
 raw (List.ofFn (fun j=>(result a (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one a.degreePrime a.degreeModFour) j)).val))
/-- The fixed original source direction list gives exactly the original source output word. -/
theorem output_eq_source {p:ℕ} (a:LPSResiduePrime p):
 output a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)=sourceOutput a:=by
 simp only [output,sourceOutput,LPSGeneratorMatrixListMachine.sourceDirections,ordered_indices]
/-- Complete actual q-only execution for every original source direction in source order. -/
noncomputable def sourceExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step (machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).program)
 ((machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).init (unary a.q))
 (some ((machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).halt (sourceOutput a)))
 ((time (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).eval (unary a.q).length):=by
 have h:=exec a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)
 rw [output_eq_source] at h
 exact h
/-- Complete original source execution within the genuine PSL-carrier polynomial. -/
noncomputable def sourceBlockExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step (machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).program)
 ((machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).init (unary a.q))
 (some ((machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).halt (sourceOutput a)))
 ((blockTime (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=blockExec a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)
 rw [output_eq_source] at h
 exact h
/-- One actual finite program for the original fixed p+1 source directions. -/
noncomputable def sourceComputableInPolyTime {p:ℕ} (hp:p.Prime) (hp4:p%4=1):=
 computableInPolyTime (LPSGeneratorMatrixListMachine.sourceDirections hp hp4)
/-- The original source collector has exactly p+1 index fields. -/
theorem source_indices_length {p:ℕ} (a:LPSResiduePrime p):
 (indices a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).length=p+1:=by
 rw [indices_length,LPSGeneratorMatrixListMachine.sourceDirections_length]
/-- All original source generator index fields are distinct. -/
theorem source_indices_nodup {p:ℕ} (a:LPSResiduePrime p):
 (indices a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).Nodup:=
 indices_nodup a _ (LPSGeneratorMatrixListMachine.sourceDirections_nodup _ _)
/-- Every original normalized source generator occurs in the computed ordered index list. -/
theorem source_indices_complete {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 (result a t).val∈indices a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour):=by
 apply List.mem_map.mpr
 exact ⟨t,LPSGeneratorMatrixListMachine.sourceDirections_complete _ _ t,rfl⟩
/-- Effective-family indices decode to the exact original source family labels. -/
theorem source_direction_decode {p:ℕ} (hp:p.Prime) (hp4:p%4=1) (n:ℕ) (j:Fin (p+1)):
 (lpsPSLEnumerationEquiv (lpsEffectiveResiduePrimeAt hp hp4 n).q)
 (result (lpsEffectiveResiduePrimeAt hp hp4 n) (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4) j))=
 lpsFinQuaternionFamilyLabel hp hp4 (card_lpsQuaternionShell_eq_prime_add_one hp hp4) n j:=by
 rw [result_decode]
 rfl
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
