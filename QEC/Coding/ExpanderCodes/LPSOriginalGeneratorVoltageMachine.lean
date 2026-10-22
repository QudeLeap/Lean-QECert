import QEC.Coding.ExpanderCodes.LPSOriginalGeneratorIndexMachine
import QEC.Coding.ExpanderCodes.LPSSparseCSS

/-!
# Actual q-only original sparse-CSS voltages

The actual collector computes the original ordered generator indices, runs the original
identity-index program on the retained q, and emits the entire identity/generator table.
Each table field is proved equal to the existing sparse-CSS double-cover voltage. Fixed
side/direction entry programs compute either original identity or original generator index
from q, with complete clean execution and standard true-PSL-carrier polynomial certificates.

The graph arithmetic prime is independent of the arbitrary fixed code field. This closes
voltage computation used by both sparse boundary rows, while complete row traversal and
scalar/physical-coordinate output and unconditional strong centered-theta growth remain
owned requirements of the exact PK22 main theorem. Source: original LPS directions and
`panteleev-kalachev-2021-good/main.tex:589-620` double-cover lifted Tanner voltage convention.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Exact identity-then-generator index table specification; no table is supplied to execution. -/
def entries {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):List ℕ:=
 (lpsPSLIndexOne a.q).val::Ordered.indices a ts
/-- The computed voltage table contains one identity field and one field per direction. -/
theorem entries_length {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 (entries a ts).length=ts.length+1:=by simp [entries,Ordered.indices_length]
/-- Fixed finite program for actual identity-index computation on the selected final q with the whole stream retained. -/
def identityQuery (n:ℕ):=RetainedFieldComputation.machine n (ModulusQuery.mask n) Identity.machine
/-- Polynomial counting actual identity-index computation on the selected final q with the whole stream retained. -/
noncomputable def identityQueryTime (n:ℕ):=RetainedFieldComputation.time n (ModulusQuery.mask n) Identity.machine Identity.time
/-- Prove complete clean execution of actual identity-index computation on the selected final q with the whole stream retained. -/
noncomputable def identityQueryExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (identityQuery ts.length).program)
 ((identityQuery ts.length).init (stream (Ordered.indices a ts++[a.q])))
 (some ((identityQuery ts.length).halt (stream (entries a ts++[a.q]))))
 ((identityQueryTime ts.length).eval (stream (Ordered.indices a ts++[a.q])).length):=by
 have hf:=MatrixListQuery.selectLast ts.length 0 (Ordered.indices a ts) a.q (by simpa using Ordered.indices_length a ts)
 have he:raw [a.q]=unary a.q:=by simpa [stream] using raw_append_last [] a.q
 have hr:raw [(lpsPSLIndexOne a.q).val]=unary (lpsPSLIndexOne a.q).val:=by
  simpa [stream] using raw_append_last [] (lpsPSLIndexOne a.q).val
 have hb:EvalsToInTime (TM2.step Identity.machine.program)
  (Identity.machine.init (raw (fields ts.length (ModulusQuery.mask ts.length) 0 (Ordered.indices a ts++[a.q]))))
  (some (Identity.machine.halt (raw [(lpsPSLIndexOne a.q).val])))
  (Identity.time.eval (raw (fields ts.length (ModulusQuery.mask ts.length) 0 (Ordered.indices a ts++[a.q]))).length):=by
  rw [hf,he,hr]
  exact Identity.exec ⟨a.q,a.prime⟩
 have h:=RetainedFieldComputation.exec ts.length (ModulusQuery.mask ts.length) Identity.machine
  (Ordered.indices a ts++[a.q]) [(lpsPSLIndexOne a.q).val] (by simp [Ordered.indices_length]) (by simp) Identity.time hb
 rw [←MatrixListQuery.stream_append] at h
 exact h
/-- Fixed finite program for actual tail-first ordered direction collection with the varying q retained. -/
def collector {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine (Ordered.collector ts) (identityQuery ts.length)
/-- Polynomial counting actual tail-first ordered direction collection with the varying q retained. -/
noncomputable def collectorTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial (Ordered.collector ts) (Ordered.collectorTime ts) (identityQueryTime ts.length)
/-- Prove complete clean execution of actual tail-first ordered direction collection with the varying q retained. -/
noncomputable def collectorExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (collector ts).program) ((collector ts).init (stream [a.q]))
 (some ((collector ts).halt (stream (entries a ts++[a.q])))) ((collectorTime ts).eval (stream [a.q]).length):=
 RetainedFieldComputation.composeRuns (Ordered.collector ts) (identityQuery ts.length) _ _ _
  (Ordered.collectorTime ts) (identityQueryTime ts.length) (Ordered.collectorExec a ts) (identityQueryExec a ts)
/-- Fixed finite program for actual fixed field projection discarding only the retained final modulus. -/
def projector {p:ℕ} (ts:List (LPSGeneratorIndex p)):=FieldProjection.machine (ts.length+1) (MatrixListQuery.prefixMask (ts.length+1))
/-- Prove complete clean execution of actual fixed field projection discarding only the retained final modulus. -/
noncomputable def projectorExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (projector ts).program) ((projector ts).init (stream (entries a ts++[a.q])))
 (some ((projector ts).halt (raw (entries a ts)))) (FieldProjection.time.eval (stream (entries a ts++[a.q])).length):=by
 have h:=FieldProjection.polyExec (ts.length+1) (MatrixListQuery.prefixMask (ts.length+1)) (entries a ts++[a.q]) (by simp [entries_length])
 rw [MatrixListQuery.selectPrefix (ts.length+1) 0 (entries a ts) a.q (by simpa using entries_length a ts)] at h
 exact h
/-- Fixed finite program for actual complete retained collection followed by final raw-output projection. -/
def collected {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine (collector ts) (projector ts)
/-- Polynomial counting actual complete retained collection followed by final raw-output projection. -/
noncomputable def collectedTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial (collector ts) (collectorTime ts) FieldProjection.time
/-- Prove complete clean execution of actual complete retained collection followed by final raw-output projection. -/
noncomputable def collectedExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (collected ts).program) ((collected ts).init (stream [a.q]))
 (some ((collected ts).halt (raw (entries a ts)))) ((collectedTime ts).eval (stream [a.q]).length):=
 RetainedFieldComputation.composeRuns (collector ts) (projector ts) _ _ _ (collectorTime ts) FieldProjection.time (collectorExec a ts) (projectorExec a ts)
/-- Fixed finite program for the complete actual q-only original index or voltage-table program. -/
def machine {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine BitDelimiter.machine (collected ts)
/-- Polynomial counting the complete actual q-only original index or voltage-table program. -/
noncomputable def time {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial BitDelimiter.machine (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (collectedTime ts)
/-- Exact original index or ordered table Boolean output specification. -/
def output {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):List Bool:=raw (entries a ts)
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
/-- Unary prime input faithfully distinguishes every varying legal graph input. -/
theorem input_injective (p:ℕ):Function.Injective (fun a:LPSResiduePrime p=>unary a.q):=LPSOriginalGeneratorIndexMachine.input_injective p
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
/-- Every computed voltage table entry is below the genuine original PSL cardinality. -/
theorem entry_lt_card {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) (v:ℕ) (hv:v∈entries a ts):
 v<Fintype.card PSL(2,ZMod a.q):=by
 have hlen: (lpsPSLList a.q).length=Fintype.card PSL(2,ZMod a.q):=LPSOriginalPSLLookupMachine.original_length_card a.q
 rcases List.mem_cons.mp hv with he|hg
 · subst v
   exact (lpsPSLIndexOne a.q).isLt.trans_le hlen.le
 · rcases List.mem_map.mp hg with ⟨t,_,he⟩
   subst v
   exact (result a t).isLt.trans_le hlen.le
/-- Identity occupies field zero and source directions retain their original order. -/
theorem ordered_entries {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p):
 entries a (List.ofFn g)=(lpsPSLIndexOne a.q).val::List.ofFn (fun j=>(result a (g j)).val):=by
 rw [entries,Ordered.ordered_indices]
/-- Fixed side/direction table selector uses field zero or one plus the direction index. -/
def fieldIndex {D:ℕ} (side:Fin 2) (j:Fin D):Fin (D+1):=
 if side=0 then 0 else ⟨j.val+1,by omega⟩
/-- Side zero selects precisely the identity field. -/
theorem fieldIndex_zero {D:ℕ} (j:Fin D):fieldIndex 0 j=0:=by simp [fieldIndex]
/-- Side one selects precisely the corresponding ordered generator field. -/
theorem fieldIndex_one {D:ℕ} (j:Fin D):fieldIndex 1 j=⟨j.val+1,by omega⟩:=by simp [fieldIndex]
/-- Each exact table field equals the existing sparse-CSS voltage index. -/
theorem entry_eq_sparseVoltage {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 (entries a (List.ofFn g))[(fieldIndex side j).val]'(by rw [entries_length,List.length_ofFn]; exact (fieldIndex side j).isLt)=
 (lpsSparseVoltage (fun j=>result a (g j)) side j).val:=by
 simp only [ordered_entries]
 by_cases hs:side=0
 · simp [fieldIndex,lpsSparseVoltage,hs]
 · simp [fieldIndex,lpsSparseVoltage,hs]
/-- Computed sparse voltages decode to the original source double-cover group labels. -/
theorem entry_decode {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 (lpsPSLEnumerationEquiv a.q) (lpsSparseVoltage (fun j=>result a (g j)) side j)=
 doubleCoverVoltage (fun j=>lpsQuaternionLabel a (g j)) side j:=by
 rw [lpsSparseVoltage_decode]
 simp only [result_decode]
/-- Exact original source-ordered index output specification, independent of execution control. -/
noncomputable def sourceOutput {p:ℕ} (a:LPSResiduePrime p):List Bool:=
 raw ((lpsPSLIndexOne a.q).val::List.ofFn (fun j=>(result a (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one a.degreePrime a.degreeModFour) j)).val))
/-- The fixed original source direction list gives exactly the original source output word. -/
theorem output_eq_source {p:ℕ} (a:LPSResiduePrime p):
 output a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)=sourceOutput a:=by
 simp only [output,sourceOutput,LPSGeneratorMatrixListMachine.sourceDirections,ordered_entries]
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
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Actual fixed side/direction program executes identity or original generator indexing. -/
def entryMachine {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):=
 if side=0 then Identity.machine else LPSOriginalGeneratorIndexMachine.machine (g j)
/-- Actual identity or generator polynomial for a fixed sparse-CSS side/direction. -/
noncomputable def entryTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):=
 if side=0 then Identity.time else LPSOriginalGeneratorIndexMachine.time (g j)
/-- Complete actual q-only computation of the exact existing sparse-CSS voltage. -/
noncomputable def entryExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 EvalsToInTime (TM2.step (entryMachine g side j).program) ((entryMachine g side j).init (unary a.q))
 (some ((entryMachine g side j).halt (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val)))
 ((entryTime g side j).eval (unary a.q).length):=by
 by_cases hs:side=0
 · have hm:entryMachine g side j=Identity.machine:=if_pos hs
   have ht:entryTime g side j=Identity.time:=if_pos hs
   rw [hm,ht]
   simp only [lpsSparseVoltage,if_pos hs]
   exact Identity.exec ⟨a.q,a.prime⟩
 · have hm:entryMachine g side j=LPSOriginalGeneratorIndexMachine.machine (g j):=if_neg hs
   have ht:entryTime g side j=LPSOriginalGeneratorIndexMachine.time (g j):=if_neg hs
   rw [hm,ht]
   simp only [lpsSparseVoltage,if_neg hs]
   exact LPSOriginalGeneratorIndexMachine.exec a (g j)
/-- Standard Mathlib certificate for the actual individual sparse-CSS voltage program. -/
noncomputable def entryOutputsInTime {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 TM2OutputsInTime (entryMachine g side j).toFinTM2 (unary a.q)
 (some (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val)) ((entryTime g side j).eval (unary a.q).length):=
 Machine.outputsInTime (entryMachine g side j) _ _ _ (entryExec a g side j)
/-- Fixed actual q-only finite program computes the exact sparse-CSS voltage in polynomial time. -/
noncomputable def entryComputableInPolyTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id
 (fun a=>unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val) where
 tm:=(entryMachine g side j).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=entryTime g side j
 outputsFun:=fun a=>by
  change TM2OutputsInTime (entryMachine g side j).toFinTM2 (List.map id (unary a.q))
   (some (List.map id (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val))) ((entryTime g side j).eval (unary a.q).length)
  have h:=entryOutputsInTime a g side j
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
/-- Individual sparse-CSS voltage polynomial after true PSL-carrier substitution. -/
noncomputable def entryBlockTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):Polynomial ℕ:=
 (entryTime g side j).comp (Polynomial.C 2*Polynomial.X)
/-- Complete individual voltage execution within its genuine PSL-carrier polynomial. -/
noncomputable def entryBlockExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 EvalsToInTime (TM2.step (entryMachine g side j).program) ((entryMachine g side j).init (unary a.q))
 (some ((entryMachine g side j).halt (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val)))
 ((entryBlockTime g side j).eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=entryExec a g side j
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [entryBlockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone (entryTime g side j) (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
/-- Standard actual individual voltage certificate at the genuine PSL-carrier budget. -/
noncomputable def entryBlockOutputsInTime {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 TM2OutputsInTime (entryMachine g side j).toFinTM2 (unary a.q)
 (some (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val)) ((entryBlockTime g side j).eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime (entryMachine g side j) _ _ _ (entryBlockExec a g side j)
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
