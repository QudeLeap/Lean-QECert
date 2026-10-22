import QEC.Coding.BitTuring.UnaryRetainedFieldComputation
import QEC.Coding.ExpanderCodes.LPSOriginalPSLLookupMachine
import QEC.Coding.ExpanderCodes.LPSSLInverseMachine

/-!
# Actual original PSL index multiplication and inverse

Only a prime and original finite vertex indices enter the fixed finite programs. They generate
their own original LAST-occurrence representatives, physically arrange matrix-operation
queries, run the actual modular product or determinant-one adjugate, and compute the original
quotient index. All phases halt with empty scratch and reset variables. Faithful unary inputs,
standard Mathlib certificates and genuine residue-prime PSL-carrier polynomials are proved.

For multiplication, looking up the right operand first places the later left result before it;
the modular product therefore computes A*B in the original order. The graph arithmetic prime
is independent of the arbitrary code field. This internal runtime closure leaves whole sparse
CSS output and unconditional strong centered-theta growth as PK22 obligations; it does not
realize the public asymptotically good qLDPC main theorem.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Inverse
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Legal domain contains only the prime and original finite vertex indices. -/
abbrev Input:=LPSOriginalPSLLookupMachine.Input
instance (a:Input):Fact a.1.val.Prime:=⟨a.1.property⟩
/-- Original LAST representative of the supplied source index; a proof specification. -/
def matrix (a:Input):SL(2,ZMod a.1.val):=LPSOriginalPSLLookupMachine.representative a.1.val a.2
/-- Faithful delimited unary encoding of all varying original indices and the prime. -/
def input (a:Input):List Bool:=stream [a.2.val,a.1.val]
/-- Exact fields after original lookup, with index and modulus retained. -/
def afterLookup (a:Input):List ℕ:=coords a.1.val (matrix a)++[a.2.val,a.1.val]
/-- Fixed finite program for original own-list lookup with the input retained. -/
def lookup:=RetainedFieldComputation.machine 1 (PrefixProjection.allMask 1) LPSOriginalPSLLookupMachine.machine
/-- Polynomial counting original own-list lookup with the input retained. -/
noncomputable def lookupTime:=RetainedFieldComputation.time 1 (PrefixProjection.allMask 1) LPSOriginalPSLLookupMachine.machine LPSOriginalPSLLookupMachine.time
/-- Prove complete clean execution of original own-list lookup with the input retained. -/
noncomputable def lookupExec (a:Input):
 EvalsToInTime (TM2.step lookup.program) (lookup.init (input a))
 (some (lookup.halt (stream (afterLookup a)))) (lookupTime.eval (input a).length):=by
 have ha:=LPSOriginalPSLLookupMachine.exec a
 have hf:fields 1 (PrefixProjection.allMask 1) 0 [a.2.val,a.1.val]=[a.2.val,a.1.val]:=PrefixProjection.fields_all 1 0 _
 have hb:EvalsToInTime (TM2.step LPSOriginalPSLLookupMachine.machine.program)
  (LPSOriginalPSLLookupMachine.machine.init (raw (fields 1 (PrefixProjection.allMask 1) 0 [a.2.val,a.1.val])))
  (some (LPSOriginalPSLLookupMachine.machine.halt (raw (coords a.1.val (matrix a)))))
  (LPSOriginalPSLLookupMachine.time.eval (raw (fields 1 (PrefixProjection.allMask 1) 0 [a.2.val,a.1.val])).length):=by
  rw [hf]
  exact ha
 have h:=RetainedFieldComputation.exec 1 (PrefixProjection.allMask 1) LPSOriginalPSLLookupMachine.machine
  [a.2.val,a.1.val] (coords a.1.val (matrix a)) (by rfl) (by simp [coords,LPSMatrixProductMachine.fields]) LPSOriginalPSLLookupMachine.time hb
 have he:stream (coords a.1.val (matrix a))++stream [a.2.val,a.1.val]=stream (afterLookup a):=by
  rw [afterLookup,MatrixListQuery.stream_append]
 rw [he] at h
 exact h
/-- Fixed mask selects the matrix coordinates and retained final modulus. -/
def inverseMask (k:Fin 6):Bool:=decide (k.val<4∨k.val=5)
/-- The fixed inverse-query mask emits precisely matrix coordinates and modulus. -/
theorem inverse_fields (a:Input):fields 5 inverseMask 0 (afterLookup a)=coords a.1.val (matrix a)++[a.1.val]:=by
 simp [afterLookup,coords,LPSMatrixProductMachine.fields,fields,maskAt,inverseMask]
/-- Fixed finite program for physical selection and delimiting of the actual matrix-operation query. -/
def prepare:=RetainedFieldComputation.projectedMarked 5 inverseMask
/-- Polynomial counting physical selection and delimiting of the actual matrix-operation query. -/
noncomputable def prepareTime:=RetainedFieldComputation.projectedMarkedTime 5 inverseMask
/-- Prove complete clean execution of physical selection and delimiting of the actual matrix-operation query. -/
noncomputable def prepareExec (a:Input):
 EvalsToInTime (TM2.step prepare.program) (prepare.init (stream (afterLookup a)))
 (some (prepare.halt (LPSSLInverseMachine.input a.1.val (matrix a)))) (prepareTime.eval (stream (afterLookup a)).length):=by
 have h:=RetainedFieldComputation.projectedMarkedExec 5 inverseMask (afterLookup a)
  (by simp [afterLookup,coords,LPSMatrixProductMachine.fields]) (by rw [inverse_fields];simp)
 rw [inverse_fields] at h
 exact h
/-- Exact inverse coordinates followed by the original matrix and modulus. -/
def afterInverse (a:Input):List ℕ:=coords a.1.val ((matrix a)⁻¹)++coords a.1.val (matrix a)++[a.1.val]
/-- Fixed finite program for actual determinant-one modular adjugate with original matrix and modulus retained. -/
def invert:=RetainedFieldComputation.retainedMarked ModularAdjugate.inverseMachine
/-- Polynomial counting actual determinant-one modular adjugate with original matrix and modulus retained. -/
noncomputable def invertTime:=RetainedFieldComputation.retainedMarkedTime ModularAdjugate.inverseMachine ModularAdjugate.time
/-- Prove complete clean execution of actual determinant-one modular adjugate with original matrix and modulus retained. -/
noncomputable def invertExec (a:Input):
 EvalsToInTime (TM2.step invert.program) (invert.init (LPSSLInverseMachine.input a.1.val (matrix a)))
 (some (invert.halt (stream (afterInverse a)))) (invertTime.eval (LPSSLInverseMachine.input a.1.val (matrix a)).length):=by
 have h:=RetainedFieldComputation.retainedMarkedExec ModularAdjugate.inverseMachine
  (LPSSLInverseMachine.input a.1.val (matrix a)) (coords a.1.val ((matrix a)⁻¹))
  (by simp [coords,LPSMatrixProductMachine.fields]) ModularAdjugate.time (LPSSLInverseMachine.polyExec a.1.val a.1.property.pos (matrix a))
 have he:stream (coords a.1.val ((matrix a)⁻¹))++LPSSLInverseMachine.input a.1.val (matrix a)=stream (afterInverse a):=by
  simp only [LPSSLInverseMachine.input,coords,afterInverse,MatrixListQuery.stream_append,List.append_assoc]
 rw [he] at h
 exact h
/-- Fixed finite program for actual copying of the final modulus to the front of the retained stream. -/
def retainModulus:=ModularAdjugate.retainedUnary 8 (ModulusQuery.mask 8)
/-- Prove complete clean execution of actual copying of the final modulus to the front of the retained stream. -/
noncomputable def retainModulusExec (a:Input):
 EvalsToInTime (TM2.step retainModulus.program) (retainModulus.init (stream (afterInverse a)))
 (some (retainModulus.halt (stream (a.1.val::afterInverse a))))
 (ModularAdjugate.stageTime.eval (stream (afterInverse a)).length):=by
 have hh:(coords a.1.val ((matrix a)⁻¹)++coords a.1.val (matrix a)).length=8:=by simp [coords,LPSMatrixProductMachine.fields]
 exact ModularAdjugate.unaryStageExec 8 (ModulusQuery.mask 8) (afterInverse a)
  (by simp [afterInverse,coords,LPSMatrixProductMachine.fields]) a.1.val (MatrixListQuery.selectLast 8 0 _ a.1.val (by simpa using hh))
/-- Fixed mask selects the front modulus and four newly computed coordinates. -/
def firstFive (k:Fin 10):Bool:=decide (k.val<5)
/-- The fixed index-query mask selects the modulus and actual result coordinates. -/
theorem first_five_fields (a:Input):fields 9 firstFive 0 (a.1.val::afterInverse a)=a.1.val::coords a.1.val ((matrix a)⁻¹):=by
 simp [afterInverse,coords,LPSMatrixProductMachine.fields,fields,maskAt,firstFive]
/-- Fixed finite program for actual first-five field selection and bit reversal to the original index query. -/
def prepareIndex:=RetainedFieldComputation.projectedReverse 9 firstFive
/-- Polynomial counting actual first-five field selection and bit reversal to the original index query. -/
noncomputable def prepareIndexTime:=RetainedFieldComputation.projectedReverseTime 9 firstFive
/-- Prove complete clean execution of actual first-five field selection and bit reversal to the original index query. -/
noncomputable def prepareIndexExec (a:Input):
 EvalsToInTime (TM2.step prepareIndex.program) (prepareIndex.init (stream (a.1.val::afterInverse a)))
 (some (prepareIndex.halt (LPSOriginalPSLIndexMachine.input ⟨a.1,(matrix a)⁻¹⟩)))
 (prepareIndexTime.eval (stream (a.1.val::afterInverse a)).length):=by
 have h:=RetainedFieldComputation.projectedReverseExec 9 firstFive (a.1.val::afterInverse a)
  (by simp [afterInverse,coords,LPSMatrixProductMachine.fields])
 rw [first_five_fields] at h
 have he:(raw (a.1.val::coords a.1.val ((matrix a)⁻¹))).reverse=LPSOriginalPSLIndexMachine.input ⟨a.1,(matrix a)⁻¹⟩:=by
  have hi:=LPSOriginalPSLIndexMachine.Initializer.input_reverse ⟨a.1,(matrix a)⁻¹⟩
  change (LPSOriginalPSLIndexMachine.Initializer.input ⟨a.1,(matrix a)⁻¹⟩).reverse=raw (a.1.val::coords a.1.val ((matrix a)⁻¹)) at hi
  rw [←hi,List.reverse_reverse]
  rfl
 rw [he] at h
 exact h
/-- Unary specification of the exact original finite quotient group-operation index. -/
def output (a:Input):List Bool:=unary (lpsPSLIndexInv a.1.val a.2).val
/-- Quotient multiplication or inversion and representative decoding give the original index. -/
theorem source_output (a:Input):LPSOriginalPSLIndexMachine.output ⟨a.1,(matrix a)⁻¹⟩=output a:=by
 have hi:quotient a.1.val ((matrix a)⁻¹)=(quotient a.1.val (matrix a))⁻¹:=by simp [quotient]
 have hd:quotient a.1.val (matrix a)=lpsPSLEnumerationEquiv a.1.val a.2:=LPSOriginalPSLLookupMachine.representative_decode _ _
 simp only [LPSOriginalPSLIndexMachine.output,hi,hd,output,lpsPSLIndexInv]
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Inverse
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Inverse
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Fixed finite program for actual original matrix-to-index computation after physical query preparation. -/
def indexed:=Composition.machine prepareIndex LPSOriginalPSLIndexMachine.machine
/-- Polynomial counting actual original matrix-to-index computation after physical query preparation. -/
noncomputable def indexedTime:=Composition.timePolynomial prepareIndex prepareIndexTime LPSOriginalPSLIndexMachine.time
/-- Prove complete clean execution of actual original matrix-to-index computation after physical query preparation. -/
noncomputable def indexedExec (a:Input):
 EvalsToInTime (TM2.step indexed.program) (indexed.init (stream (a.1.val::afterInverse a)))
 (some (indexed.halt (output a))) (indexedTime.eval (stream (a.1.val::afterInverse a)).length):=by
 have h:=LPSOriginalPSLIndexMachine.exec ⟨a.1,(matrix a)⁻¹⟩
 rw [source_output] at h
 exact RetainedFieldComputation.composeRuns prepareIndex LPSOriginalPSLIndexMachine.machine _ _ _ prepareIndexTime LPSOriginalPSLIndexMachine.time (prepareIndexExec a) h
/-- Fixed finite program for actual modulus copy followed by complete original indexing. -/
def modulusAndIndex:=Composition.machine retainModulus indexed
/-- Polynomial counting actual modulus copy followed by complete original indexing. -/
noncomputable def modulusAndIndexTime:=Composition.timePolynomial retainModulus ModularAdjugate.stageTime indexedTime
/-- Prove complete clean execution of actual modulus copy followed by complete original indexing. -/
noncomputable def modulusAndIndexExec (a:Input):
 EvalsToInTime (TM2.step modulusAndIndex.program) (modulusAndIndex.init (stream (afterInverse a)))
 (some (modulusAndIndex.halt (output a))) (modulusAndIndexTime.eval (stream (afterInverse a)).length):=
 RetainedFieldComputation.composeRuns retainModulus indexed _ _ _ ModularAdjugate.stageTime indexedTime (retainModulusExec a) (indexedExec a)
/-- Fixed finite program for actual inverse computation followed by modulus restoration and original indexing. -/
def inversionAndIndex:=Composition.machine invert modulusAndIndex
/-- Polynomial counting actual inverse computation followed by modulus restoration and original indexing. -/
noncomputable def inversionAndIndexTime:=Composition.timePolynomial invert invertTime modulusAndIndexTime
/-- Prove complete clean execution of actual inverse computation followed by modulus restoration and original indexing. -/
noncomputable def inversionAndIndexExec (a:Input):
 EvalsToInTime (TM2.step inversionAndIndex.program) (inversionAndIndex.init (LPSSLInverseMachine.input a.1.val (matrix a)))
 (some (inversionAndIndex.halt (output a))) (inversionAndIndexTime.eval (LPSSLInverseMachine.input a.1.val (matrix a)).length):=
 RetainedFieldComputation.composeRuns invert modulusAndIndex _ _ _ invertTime modulusAndIndexTime (invertExec a) (modulusAndIndexExec a)
/-- Fixed finite program for actual inverse-query preparation followed by complete inverse indexing. -/
def preparedInverseIndex:=Composition.machine prepare inversionAndIndex
/-- Polynomial counting actual inverse-query preparation followed by complete inverse indexing. -/
noncomputable def preparedInverseIndexTime:=Composition.timePolynomial prepare prepareTime inversionAndIndexTime
/-- Prove complete clean execution of actual inverse-query preparation followed by complete inverse indexing. -/
noncomputable def preparedInverseIndexExec (a:Input):
 EvalsToInTime (TM2.step preparedInverseIndex.program) (preparedInverseIndex.init (stream (afterLookup a)))
 (some (preparedInverseIndex.halt (output a))) (preparedInverseIndexTime.eval (stream (afterLookup a)).length):=
 RetainedFieldComputation.composeRuns prepare inversionAndIndex _ _ _ prepareTime inversionAndIndexTime (prepareExec a) (inversionAndIndexExec a)
/-- Fixed finite program for the complete actual original source index operation. -/
def machine:=Composition.machine lookup preparedInverseIndex
/-- Polynomial counting the complete actual original source index operation. -/
noncomputable def time:=Composition.timePolynomial lookup lookupTime preparedInverseIndexTime
/-- Prove complete clean execution of the complete actual original source index operation. -/
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
 (some (machine.halt (output a))) (time.eval (input a).length):=
 RetainedFieldComputation.composeRuns lookup preparedInverseIndex _ _ _ lookupTime preparedInverseIndexTime (lookupExec a) (preparedInverseIndexExec a)
/-- Standard Mathlib certificate for the complete actual original-index operation. -/
noncomputable def outputsInTime (a:Input):
 TM2OutputsInTime machine.toFinTM2 (input a) (some (output a)) (time.eval (input a).length):=
 Machine.outputsInTime machine _ _ _ (exec a)
/-- One fixed actual finite program computes all legal source indices in polynomial time. -/
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
/-- Input bits faithfully distinguish every varying prime and original index. -/
theorem input_injective:Function.Injective input:=by
 intro a b hab
 have hh:=stream_injective hab
 rcases a with ⟨⟨q,hq⟩,i⟩
 rcases b with ⟨⟨r,hr⟩,j⟩
 simp only [List.cons.injEq] at hh
 rcases hh with ⟨hij,hqr,_⟩
 subst r
 have hi:i=j:=Fin.ext hij
 subst j
 rfl
/-- Exact size of the actual unary index/prime input. -/
theorem input_length (a:Input):(input a).length=a.2.val+a.1.val+2:=by
 simp only [input,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
 omega
/-- The emitted original finite index is strictly below the genuine PSL cardinality. -/
theorem output_length_lt_card (a:Input):(output a).length<Fintype.card PSL(2,ZMod a.1.val):=by
 have h:((lpsPSLIndexInv a.1.val a.2).val)<(lpsPSLList a.1.val).length:=(lpsPSLIndexInv a.1.val a.2).isLt
 have hc:=LPSOriginalPSLLookupMachine.original_length_card a.1.val
 have hh:=h.trans_le hc.le
 simpa only [output,unary_length] using hh
/-- Whole operation polynomial after genuine residue-prime carrier substitution. -/
noncomputable def blockTime:Polynomial ℕ:=time.comp (Polynomial.C 3*Polynomial.X+Polynomial.C 2)
/-- Complete clean actual source execution within the genuine PSL-carrier polynomial. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (i:Fin (lpsPSLList a.q).length):
 EvalsToInTime (TM2.step machine.program) (machine.init (input ⟨⟨a.q,a.prime⟩,i⟩))
 (some (machine.halt (output ⟨⟨a.q,a.prime⟩,i⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨⟨a.q,a.prime⟩,i⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hL:(input ⟨⟨a.q,a.prime⟩,i⟩).length≤3*Fintype.card PSL(2,ZMod a.q)+2:=by
  rw [input_length]
  change i.val+a.q+2≤3*Fintype.card PSL(2,ZMod a.q)+2
  have hi:i.val<Fintype.card PSL(2,ZMod a.q):=i.isLt.trans_le (LPSOriginalPSLLookupMachine.original_length_card a.q).le
  have hq:=a.q_le_two_mul_card_psl
  omega
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time hL
/-- Standard actual output certificate at the genuine PSL-carrier budget. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (i:Fin (lpsPSLList a.q).length):
 TM2OutputsInTime machine.toFinTM2 (input ⟨⟨a.q,a.prime⟩,i⟩) (some (output ⟨⟨a.q,a.prime⟩,i⟩))
 (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a i)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Inverse
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Multiply
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
/-- Legal domain contains only the prime and original finite vertex indices. -/
abbrev Input:=Σ q:{q:ℕ//q.Prime},Fin (lpsPSLList q.val).length×Fin (lpsPSLList q.val).length
instance (a:Input):Fact a.1.val.Prime:=⟨a.1.property⟩
/-- Original LAST representative of the left source index; never supplied to initialization. -/
def left (a:Input):SL(2,ZMod a.1.val):=LPSOriginalPSLLookupMachine.representative a.1.val a.2.1
/-- Original LAST representative of the right source index; never supplied to initialization. -/
def right (a:Input):SL(2,ZMod a.1.val):=LPSOriginalPSLLookupMachine.representative a.1.val a.2.2
/-- Faithful delimited unary encoding of all varying original indices and the prime. -/
def input (a:Input):List Bool:=stream [a.2.1.val,a.2.2.val,a.1.val]
/-- Exact right matrix followed by both original indices and the modulus. -/
def afterRight (a:Input):List ℕ:=coords a.1.val (right a)++[a.2.1.val,a.2.2.val,a.1.val]
/-- Fixed mask selects the right index and prime from the three input fields. -/
def rightMask (k:Fin 3):Bool:=decide (1≤k.val)
/-- The actual right-query mask selects precisely the original right index and prime. -/
theorem right_fields (a:Input):fields 2 rightMask 0 [a.2.1.val,a.2.2.val,a.1.val]=[a.2.2.val,a.1.val]:=by
 simp [fields,maskAt,rightMask]
/-- Fixed finite program for original right-index own-list lookup with both indices retained. -/
def lookupRight:=RetainedFieldComputation.machine 2 rightMask LPSOriginalPSLLookupMachine.machine
/-- Polynomial counting original right-index own-list lookup with both indices retained. -/
noncomputable def lookupRightTime:=RetainedFieldComputation.time 2 rightMask LPSOriginalPSLLookupMachine.machine LPSOriginalPSLLookupMachine.time
/-- Prove complete clean execution of original right-index own-list lookup with both indices retained. -/
noncomputable def lookupRightExec (a:Input):
 EvalsToInTime (TM2.step lookupRight.program) (lookupRight.init (input a))
 (some (lookupRight.halt (stream (afterRight a)))) (lookupRightTime.eval (input a).length):=by
 have hb:EvalsToInTime (TM2.step LPSOriginalPSLLookupMachine.machine.program)
  (LPSOriginalPSLLookupMachine.machine.init (raw (fields 2 rightMask 0 [a.2.1.val,a.2.2.val,a.1.val])))
  (some (LPSOriginalPSLLookupMachine.machine.halt (raw (coords a.1.val (right a)))))
  (LPSOriginalPSLLookupMachine.time.eval (raw (fields 2 rightMask 0 [a.2.1.val,a.2.2.val,a.1.val])).length):=by
  rw [right_fields]
  exact LPSOriginalPSLLookupMachine.exec ⟨a.1,a.2.2⟩
 have h:=RetainedFieldComputation.exec 2 rightMask LPSOriginalPSLLookupMachine.machine
  [a.2.1.val,a.2.2.val,a.1.val] (coords a.1.val (right a)) (by rfl)
  (by simp [coords,LPSMatrixProductMachine.fields]) LPSOriginalPSLLookupMachine.time hb
 have he:stream (coords a.1.val (right a))++stream [a.2.1.val,a.2.2.val,a.1.val]=stream (afterRight a):=by
  rw [afterRight,MatrixListQuery.stream_append]
 rw [he] at h
 exact h
/-- Exact left then right matrices, followed by original indices and modulus. -/
def afterLeft (a:Input):List ℕ:=coords a.1.val (left a)++afterRight a
/-- Fixed mask selects the left index and prime after retaining the right matrix. -/
def leftMask (k:Fin 7):Bool:=decide (k.val=4∨k.val=6)
/-- The actual left-query mask selects precisely the original left index and prime. -/
theorem left_fields (a:Input):fields 6 leftMask 0 (afterRight a)=[a.2.1.val,a.1.val]:=by
 simp [afterRight,coords,LPSMatrixProductMachine.fields,fields,maskAt,leftMask]
/-- Fixed finite program for original left-index own-list lookup preserving the earlier right matrix. -/
def lookupLeft:=RetainedFieldComputation.machine 6 leftMask LPSOriginalPSLLookupMachine.machine
/-- Polynomial counting original left-index own-list lookup preserving the earlier right matrix. -/
noncomputable def lookupLeftTime:=RetainedFieldComputation.time 6 leftMask LPSOriginalPSLLookupMachine.machine LPSOriginalPSLLookupMachine.time
/-- Prove complete clean execution of original left-index own-list lookup preserving the earlier right matrix. -/
noncomputable def lookupLeftExec (a:Input):
 EvalsToInTime (TM2.step lookupLeft.program) (lookupLeft.init (stream (afterRight a)))
 (some (lookupLeft.halt (stream (afterLeft a)))) (lookupLeftTime.eval (stream (afterRight a)).length):=by
 have hb:EvalsToInTime (TM2.step LPSOriginalPSLLookupMachine.machine.program)
  (LPSOriginalPSLLookupMachine.machine.init (raw (fields 6 leftMask 0 (afterRight a))))
  (some (LPSOriginalPSLLookupMachine.machine.halt (raw (coords a.1.val (left a)))))
  (LPSOriginalPSLLookupMachine.time.eval (raw (fields 6 leftMask 0 (afterRight a))).length):=by
  rw [left_fields]
  exact LPSOriginalPSLLookupMachine.exec ⟨a.1,a.2.1⟩
 have h:=RetainedFieldComputation.exec 6 leftMask LPSOriginalPSLLookupMachine.machine
  (afterRight a) (coords a.1.val (left a)) (by simp [afterRight,coords,LPSMatrixProductMachine.fields])
  (by simp [coords,LPSMatrixProductMachine.fields]) LPSOriginalPSLLookupMachine.time hb
 have he:stream (coords a.1.val (left a))++stream (afterRight a)=stream (afterLeft a):=by
  rw [afterLeft,MatrixListQuery.stream_append]
 rw [he] at h
 exact h
/-- Fixed mask selects left coordinates, right coordinates and the final modulus. -/
def productMask (k:Fin 11):Bool:=decide (k.val<8∨k.val=10)
/-- The fixed product-query mask preserves left-before-right operand order. -/
theorem product_fields (a:Input):fields 10 productMask 0 (afterLeft a)=coords a.1.val (left a)++coords a.1.val (right a)++[a.1.val]:=by
 simp [afterLeft,afterRight,coords,LPSMatrixProductMachine.fields,fields,maskAt,productMask]
/-- Fixed finite program for physical selection and delimiting of the actual matrix-operation query. -/
def prepare:=RetainedFieldComputation.projectedMarked 10 productMask
/-- Polynomial counting physical selection and delimiting of the actual matrix-operation query. -/
noncomputable def prepareTime:=RetainedFieldComputation.projectedMarkedTime 10 productMask
/-- Prove complete clean execution of physical selection and delimiting of the actual matrix-operation query. -/
noncomputable def prepareExec (a:Input):
 EvalsToInTime (TM2.step prepare.program) (prepare.init (stream (afterLeft a)))
 (some (prepare.halt (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val)))
 (prepareTime.eval (stream (afterLeft a)).length):=by
 have h:=RetainedFieldComputation.projectedMarkedExec 10 productMask (afterLeft a)
  (by simp [afterLeft,afterRight,coords,LPSMatrixProductMachine.fields]) (by rw [product_fields];simp [coords,LPSMatrixProductMachine.fields])
 rw [product_fields] at h
 exact h
/-- Exact product coordinates followed by both operands and modulus. -/
def afterProduct (a:Input):List ℕ:=coords a.1.val (left a*right a)++coords a.1.val (left a)++coords a.1.val (right a)++[a.1.val]
/-- Fixed finite program for actual modular A*B multiplication with both operands and modulus retained. -/
def product:=RetainedFieldComputation.retainedMarked ModularMatrixProduct.productMachine
/-- Polynomial counting actual modular A*B multiplication with both operands and modulus retained. -/
noncomputable def productTime:=RetainedFieldComputation.retainedMarkedTime ModularMatrixProduct.productMachine ModularMatrixProduct.time
/-- Prove complete clean execution of actual modular A*B multiplication with both operands and modulus retained. -/
noncomputable def productExec (a:Input):
 EvalsToInTime (TM2.step product.program) (product.init (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val))
 (some (product.halt (stream (afterProduct a))))
 (productTime.eval (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val).length):=by
 have h:=RetainedFieldComputation.retainedMarkedExec ModularMatrixProduct.productMachine
  (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val) (coords a.1.val (left a*right a))
  (by simp [coords,LPSMatrixProductMachine.fields]) ModularMatrixProduct.time (LPSMatrixProductMachine.slExec a.1.val a.1.property.pos (left a) (right a))
 have he:stream (coords a.1.val (left a*right a))++LPSMatrixProductMachine.input a.1.val (left a).val (right a).val=stream (afterProduct a):=by
  simp only [LPSMatrixProductMachine.input,coords,afterProduct,MatrixListQuery.stream_append,List.append_assoc]
 rw [he] at h
 exact h
/-- Fixed finite program for actual copying of the final modulus to the front of the retained stream. -/
def retainModulus:=ModularAdjugate.retainedUnary 12 (ModulusQuery.mask 12)
/-- Prove complete clean execution of actual copying of the final modulus to the front of the retained stream. -/
noncomputable def retainModulusExec (a:Input):
 EvalsToInTime (TM2.step retainModulus.program) (retainModulus.init (stream (afterProduct a)))
 (some (retainModulus.halt (stream (a.1.val::afterProduct a))))
 (ModularAdjugate.stageTime.eval (stream (afterProduct a)).length):=by
 exact ModularAdjugate.unaryStageExec 12 (ModulusQuery.mask 12) (afterProduct a)
  (by simp [afterProduct,coords,LPSMatrixProductMachine.fields]) a.1.val
  (MatrixListQuery.selectLast 12 0 (coords a.1.val (left a*right a)++coords a.1.val (left a)++coords a.1.val (right a)) a.1.val (by simp [coords,LPSMatrixProductMachine.fields]))
/-- Fixed mask selects the front modulus and four newly computed coordinates. -/
def firstFive (k:Fin 14):Bool:=decide (k.val<5)
/-- The fixed index-query mask selects the modulus and actual result coordinates. -/
theorem first_five_fields (a:Input):fields 13 firstFive 0 (a.1.val::afterProduct a)=a.1.val::coords a.1.val (left a*right a):=by
 simp [afterProduct,coords,LPSMatrixProductMachine.fields,fields,maskAt,firstFive]
/-- Fixed finite program for actual first-five field selection and bit reversal to the original index query. -/
def prepareIndex:=RetainedFieldComputation.projectedReverse 13 firstFive
/-- Polynomial counting actual first-five field selection and bit reversal to the original index query. -/
noncomputable def prepareIndexTime:=RetainedFieldComputation.projectedReverseTime 13 firstFive
/-- Prove complete clean execution of actual first-five field selection and bit reversal to the original index query. -/
noncomputable def prepareIndexExec (a:Input):
 EvalsToInTime (TM2.step prepareIndex.program) (prepareIndex.init (stream (a.1.val::afterProduct a)))
 (some (prepareIndex.halt (LPSOriginalPSLIndexMachine.input ⟨a.1,left a*right a⟩)))
 (prepareIndexTime.eval (stream (a.1.val::afterProduct a)).length):=by
 have h:=RetainedFieldComputation.projectedReverseExec 13 firstFive (a.1.val::afterProduct a)
  (by simp [afterProduct,coords,LPSMatrixProductMachine.fields])
 rw [first_five_fields] at h
 have he:(raw (a.1.val::coords a.1.val (left a*right a))).reverse=LPSOriginalPSLIndexMachine.input ⟨a.1,left a*right a⟩:=by
  have hi:=LPSOriginalPSLIndexMachine.Initializer.input_reverse ⟨a.1,left a*right a⟩
  change (LPSOriginalPSLIndexMachine.Initializer.input ⟨a.1,left a*right a⟩).reverse=raw (a.1.val::coords a.1.val (left a*right a)) at hi
  rw [←hi,List.reverse_reverse]
  rfl
 rw [he] at h
 exact h
/-- Unary specification of the exact original finite quotient group-operation index. -/
def output (a:Input):List Bool:=unary (lpsPSLIndexMul a.1.val a.2.1 a.2.2).val
/-- Quotient multiplication or inversion and representative decoding give the original index. -/
theorem source_output (a:Input):LPSOriginalPSLIndexMachine.output ⟨a.1,left a*right a⟩=output a:=by
 have hi:quotient a.1.val (left a*right a)=quotient a.1.val (left a)*quotient a.1.val (right a):=by simp [quotient]
 have hl:quotient a.1.val (left a)=lpsPSLEnumerationEquiv a.1.val a.2.1:=LPSOriginalPSLLookupMachine.representative_decode _ _
 have hr:quotient a.1.val (right a)=lpsPSLEnumerationEquiv a.1.val a.2.2:=LPSOriginalPSLLookupMachine.representative_decode _ _
 simp only [LPSOriginalPSLIndexMachine.output,hi,hl,hr,output,lpsPSLIndexMul]
/-- Fixed finite program for actual original matrix-to-index computation after physical query preparation. -/
def indexed:=Composition.machine prepareIndex LPSOriginalPSLIndexMachine.machine
/-- Polynomial counting actual original matrix-to-index computation after physical query preparation. -/
noncomputable def indexedTime:=Composition.timePolynomial prepareIndex prepareIndexTime LPSOriginalPSLIndexMachine.time
/-- Prove complete clean execution of actual original matrix-to-index computation after physical query preparation. -/
noncomputable def indexedExec (a:Input):
 EvalsToInTime (TM2.step indexed.program) (indexed.init (stream (a.1.val::afterProduct a)))
 (some (indexed.halt (output a))) (indexedTime.eval (stream (a.1.val::afterProduct a)).length):=by
 have h:=LPSOriginalPSLIndexMachine.exec ⟨a.1,left a*right a⟩
 rw [source_output] at h
 exact RetainedFieldComputation.composeRuns prepareIndex LPSOriginalPSLIndexMachine.machine _ _ _ prepareIndexTime LPSOriginalPSLIndexMachine.time (prepareIndexExec a) (h)
/-- Fixed finite program for actual modulus copy followed by complete original indexing. -/
def modulusAndIndex:=Composition.machine retainModulus indexed
/-- Polynomial counting actual modulus copy followed by complete original indexing. -/
noncomputable def modulusAndIndexTime:=Composition.timePolynomial retainModulus ModularAdjugate.stageTime indexedTime
/-- Prove complete clean execution of actual modulus copy followed by complete original indexing. -/
noncomputable def modulusAndIndexExec (a:Input):
 EvalsToInTime (TM2.step modulusAndIndex.program) (modulusAndIndex.init (stream (afterProduct a)))
 (some (modulusAndIndex.halt (output a))) (modulusAndIndexTime.eval (stream (afterProduct a)).length):=
 RetainedFieldComputation.composeRuns retainModulus indexed _ _ _ ModularAdjugate.stageTime indexedTime (retainModulusExec a) (indexedExec a)
/-- Fixed finite program for actual product computation followed by modulus restoration and original indexing. -/
def productAndIndex:=Composition.machine product modulusAndIndex
/-- Polynomial counting actual product computation followed by modulus restoration and original indexing. -/
noncomputable def productAndIndexTime:=Composition.timePolynomial product productTime modulusAndIndexTime
/-- Prove complete clean execution of actual product computation followed by modulus restoration and original indexing. -/
noncomputable def productAndIndexExec (a:Input):
 EvalsToInTime (TM2.step productAndIndex.program) (productAndIndex.init (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val))
 (some (productAndIndex.halt (output a))) (productAndIndexTime.eval (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val).length):=
 RetainedFieldComputation.composeRuns product modulusAndIndex _ _ _ productTime modulusAndIndexTime (productExec a) (modulusAndIndexExec a)
/-- Fixed finite program for actual product-query preparation followed by complete product indexing. -/
def preparedProductIndex:=Composition.machine prepare productAndIndex
/-- Polynomial counting actual product-query preparation followed by complete product indexing. -/
noncomputable def preparedProductIndexTime:=Composition.timePolynomial prepare prepareTime productAndIndexTime
/-- Prove complete clean execution of actual product-query preparation followed by complete product indexing. -/
noncomputable def preparedProductIndexExec (a:Input):
 EvalsToInTime (TM2.step preparedProductIndex.program) (preparedProductIndex.init (stream (afterLeft a)))
 (some (preparedProductIndex.halt (output a))) (preparedProductIndexTime.eval (stream (afterLeft a)).length):=
 RetainedFieldComputation.composeRuns prepare productAndIndex _ _ _ prepareTime productAndIndexTime (prepareExec a) (productAndIndexExec a)
/-- Fixed finite program for actual left lookup followed by product preparation and original product indexing. -/
def leftAndProductIndex:=Composition.machine lookupLeft preparedProductIndex
/-- Polynomial counting actual left lookup followed by product preparation and original product indexing. -/
noncomputable def leftAndProductIndexTime:=Composition.timePolynomial lookupLeft lookupLeftTime preparedProductIndexTime
/-- Prove complete clean execution of actual left lookup followed by product preparation and original product indexing. -/
noncomputable def leftAndProductIndexExec (a:Input):
 EvalsToInTime (TM2.step leftAndProductIndex.program) (leftAndProductIndex.init (stream (afterRight a)))
 (some (leftAndProductIndex.halt (output a))) (leftAndProductIndexTime.eval (stream (afterRight a)).length):=
 RetainedFieldComputation.composeRuns lookupLeft preparedProductIndex _ _ _ lookupLeftTime preparedProductIndexTime (lookupLeftExec a) (preparedProductIndexExec a)
/-- Fixed finite program for the complete actual original source index operation. -/
def machine:=Composition.machine lookupRight leftAndProductIndex
/-- Polynomial counting the complete actual original source index operation. -/
noncomputable def time:=Composition.timePolynomial lookupRight lookupRightTime leftAndProductIndexTime
/-- Prove complete clean execution of the complete actual original source index operation. -/
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
 (some (machine.halt (output a))) (time.eval (input a).length):=
 RetainedFieldComputation.composeRuns lookupRight leftAndProductIndex _ _ _ lookupRightTime leftAndProductIndexTime (lookupRightExec a) (leftAndProductIndexExec a)
/-- Standard Mathlib certificate for the complete actual original-index operation. -/
noncomputable def outputsInTime (a:Input):
 TM2OutputsInTime machine.toFinTM2 (input a) (some (output a)) (time.eval (input a).length):=
 Machine.outputsInTime machine _ _ _ (exec a)
/-- One fixed actual finite program computes all legal source indices in polynomial time. -/
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
/-- Input bits faithfully distinguish every varying prime and original index. -/
theorem input_injective:Function.Injective input:=by
 intro a b hab
 have hh:=stream_injective hab
 rcases a with ⟨⟨q,hq⟩,i,j⟩
 rcases b with ⟨⟨r,hr⟩,k,l⟩
 simp only [List.cons.injEq] at hh
 rcases hh with ⟨hik,hjl,hqr,_⟩
 subst r
 have hi:i=k:=Fin.ext hik
 have hj:j=l:=Fin.ext hjl
 subst k
 subst l
 rfl
/-- Exact size of the actual unary index/prime input. -/
theorem input_length (a:Input):(input a).length=a.2.1.val+a.2.2.val+a.1.val+3:=by
 simp only [input,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
 omega
/-- The emitted original finite index is strictly below the genuine PSL cardinality. -/
theorem output_length_lt_card (a:Input):(output a).length<Fintype.card PSL(2,ZMod a.1.val):=by
 have h:((lpsPSLIndexMul a.1.val a.2.1 a.2.2).val)<(lpsPSLList a.1.val).length:=(lpsPSLIndexMul a.1.val a.2.1 a.2.2).isLt
 have hc:=LPSOriginalPSLLookupMachine.original_length_card a.1.val
 have hh:=h.trans_le hc.le
 simpa only [output,unary_length] using hh
/-- Whole operation polynomial after genuine residue-prime carrier substitution. -/
noncomputable def blockTime:Polynomial ℕ:=time.comp (Polynomial.C 4*Polynomial.X+Polynomial.C 3)
/-- Complete clean actual source execution within the genuine PSL-carrier polynomial. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (i j:Fin (lpsPSLList a.q).length):
 EvalsToInTime (TM2.step machine.program) (machine.init (input ⟨⟨a.q,a.prime⟩,i,j⟩))
 (some (machine.halt (output ⟨⟨a.q,a.prime⟩,i,j⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨⟨a.q,a.prime⟩,i,j⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hL:(input ⟨⟨a.q,a.prime⟩,i,j⟩).length≤4*Fintype.card PSL(2,ZMod a.q)+3:=by
  rw [input_length]
  change i.val+j.val+a.q+3≤4*Fintype.card PSL(2,ZMod a.q)+3
  have hi:i.val<Fintype.card PSL(2,ZMod a.q):=i.isLt.trans_le (LPSOriginalPSLLookupMachine.original_length_card a.q).le
  have hj:j.val<Fintype.card PSL(2,ZMod a.q):=j.isLt.trans_le (LPSOriginalPSLLookupMachine.original_length_card a.q).le
  have hq:=a.q_le_two_mul_card_psl
  omega
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time hL
/-- Standard actual output certificate at the genuine PSL-carrier budget. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (i j:Fin (lpsPSLList a.q).length):
 TM2OutputsInTime machine.toFinTM2 (input ⟨⟨a.q,a.prime⟩,i,j⟩) (some (output ⟨⟨a.q,a.prime⟩,i,j⟩))
 (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a i j)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Multiply
