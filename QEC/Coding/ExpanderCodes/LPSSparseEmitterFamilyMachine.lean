import QEC.Coding.ExpanderCodes.LPSSparseEmitterSourceMachine
import QEC.Coding.ExpanderCodes.LPSPrimeMachine

/-!
# Actual original-prime sparse-CSS family algorithm

A single finite Boolean program takes unary B, runs the existing original least eligible
prime selector and the complete original sparse emitter, and writes all scalar checks.
Its proved time is polynomial in the actual output PSL carrier and physical qudit count;
this is not a polynomial-in-B assertion. Source p+1 directions preserve the Jacobi-based
numbering and have cofinal physical lengths. Strict decoded output equals the existing
original-family checks; decoded Pauli operators cut out exactly the original CSS carrier.
Field tables/local matrices are fixed once for an arbitrary finite code field.

Source: panteleev-kalachev-2021-good/main.tex:231-238,248-273,589-620,1744.
This closes the complete sparse-output algorithm obligation. It does not prove the
unconditional strong centered-theta estimate or the public PK22 good-family theorem.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
def machine {p D r r' s:ℕ} (hp:p.Prime) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):=
 Composition.machine (lpsPrimeMachine hp) (LPSSparseEmitterSource.machine g t h h')
noncomputable def time {p D r r' s:ℕ} (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):Polynomial ℕ:=
 (ResiduePrime.fullTime+LPSSparseEmitterSource.time g t h h'+Polynomial.C 2*Polynomial.X+Polynomial.C 2).comp
 (Polynomial.C 2*Polynomial.X)
def output {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):=
 LPSSparseEmitterSource.output (lpsEffectiveResiduePrimeAt hp hp4 B) g t h h'
noncomputable def exec {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 EvalsToInTime (TM2.step (machine hp g t h h').program) ((machine hp g t h h').init (unary B))
 (some ((machine hp g t h h').halt (output hp hp4 B g t h h')))
 ((time g t h h').eval (Fintype.card PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q))):=by
 let a:=lpsEffectiveResiduePrimeAt hp hp4 B
 have hx:=Composition.executes (lpsPrimeMachine hp) (LPSSparseEmitterSource.machine g t h h') _ _ _ _ _
  (lpsPrimeMachineBlockExec hp hp4 B) (LPSSparseEmitterSource.blockExec a g t h h')
 refine {hx with steps_le_m:=hx.steps_le_m.trans ?_}
 dsimp only [a]
 simp only [time,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,unary_length]
 have hq:=a.q_le_two_mul_card_psl
 dsimp only [a] at hq
 omega
noncomputable def outputsInTime {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 TM2OutputsInTime (machine hp g t h h').toFinTM2 (unary B) (some (output hp hp4 B g t h h'))
 ((time g t h h').eval (Fintype.card PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q))):=
 Machine.outputsInTime _ _ _ _ (exec hp hp4 B g t h h')
theorem output_eq_original {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 output hp hp4 B g t h h'=LPSSparseEmitterCodec.encode
 ((lpsEncodedCheckOutput t (fun j=>lpsEffectiveQuaternionFamilyIndex hp hp4 B (g j)) h h').map
 (fun rs=>rs.map (fun e=>(e.1.val,e.2.val)))):=rfl
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open scoped MatrixGroups
theorem decodeTyped_output {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterCodec.decodeTyped
 (D*(D*(lpsPSLList (lpsEffectiveResiduePrimeAt hp hp4 B).q).length)+
 (2*r)*((2*r')*(lpsPSLList (lpsEffectiveResiduePrimeAt hp hp4 B).q).length)) s (output hp hp4 B g t h h')=
 some (lpsEncodedCheckOutput t (fun j=>lpsEffectiveQuaternionFamilyIndex hp hp4 B (g j)) h h'):=
 LPSSparseEmitterSource.decodeTyped_output _ g t h h'
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
def physicalSize {p:ℕ} (a:LPSResiduePrime p) (D r r':ℕ):ℕ:=
 Fintype.card (LiftedProduct.QubitIndex (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod a.q))
theorem physicalSize_eq {p:ℕ} (a:LPSResiduePrime p) (D r r':ℕ):
 physicalSize a D r r'=(D*D+(2*r)*(2*r'))*Fintype.card PSL(2,ZMod a.q):=by
 simp only [physicalSize,LiftedProduct.QubitIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
 ring
theorem carrier_le_physicalSize {p:ℕ} (a:LPSResiduePrime p) {D r r':ℕ} (hD:0 < D):
 Fintype.card PSL(2,ZMod a.q) ≤ physicalSize a D r r':=by
 rw [physicalSize_eq]
 have hd:1 ≤ D*D:=by nlinarith
 simpa only [Nat.one_mul] using Nat.mul_le_mul_right (Fintype.card PSL(2,ZMod a.q)) (hd.trans (Nat.le_add_right _ _))
noncomputable def physicalExec {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (hD:0 < D)
 (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 EvalsToInTime (TM2.step (machine hp g t h h').program) ((machine hp g t h h').init (unary B))
 (some ((machine hp g t h h').halt (output hp hp4 B g t h h')))
 ((time g t h h').eval (physicalSize (lpsEffectiveResiduePrimeAt hp hp4 B) D r r')):=by
 have hx:=exec hp hp4 B g t h h'
 refine {hx with steps_le_m:=hx.steps_le_m.trans ?_}
 exact Composition.polynomial_eval_monotone _ (carrier_le_physicalSize _ hD)
noncomputable def sourceDirections {p:ℕ} (hp:p.Prime) (hp4:p%4=1):Fin (p+1)→LPSGeneratorIndex p:=
 lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4)
noncomputable def sourceMachine {p r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin (p+1)) (Fin s)) (h':Matrix (Fin r') (Fin (p+1)) (Fin s)):=
 machine hp (sourceDirections hp hp4) t h h'
noncomputable def sourceTime {p r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin (p+1)) (Fin s)) (h':Matrix (Fin r') (Fin (p+1)) (Fin s)):=
 time (sourceDirections hp hp4) t h h'
noncomputable def sourceOutput {p r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin (p+1)) (Fin s)) (h':Matrix (Fin r') (Fin (p+1)) (Fin s)):=
 output hp hp4 B (sourceDirections hp hp4) t h h'
noncomputable def sourceExec {p r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin (p+1)) (Fin s)) (h':Matrix (Fin r') (Fin (p+1)) (Fin s)):
 EvalsToInTime (TM2.step (sourceMachine hp hp4 t h h').program) ((sourceMachine hp hp4 t h h').init (unary B))
 (some ((sourceMachine hp hp4 t h h').halt (sourceOutput hp hp4 B t h h')))
 ((sourceTime hp hp4 t h h').eval (physicalSize (lpsEffectiveResiduePrimeAt hp hp4 B) (p+1) r r')):=
 physicalExec hp hp4 B (by omega) (sourceDirections hp hp4) t h h'
theorem sourcePhysicalSize_cofinal {p r r':ℕ} (hp:p.Prime) (hp4:p%4=1):
 ∀ N:ℕ,∃ B,N ≤ physicalSize (lpsEffectiveResiduePrimeAt hp hp4 B) (p+1) r r':=by
 intro N
 obtain ⟨B,hB⟩:=lpsEffectiveVertexGroup_card_cofinal hp hp4 N
 exact ⟨B,hB.trans (carrier_le_physicalSize _ (by omega))⟩
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily

namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open scoped MatrixGroups
open FiniteFieldPauli
noncomputable local instance {q D r r':ℕ} [Fact q.Prime]:DecidableEq
 (LiftedProduct.QubitIndex (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod q)):=Classical.decEq _
abbrev PhysicalCount (q D r r':ℕ) [Fact q.Prime]:=D*(D*(lpsPSLList q).length)+(2*r)*((2*r')*(lpsPSLList q).length)
abbrev CheckCount (q D r r' s:ℕ) [Fact q.Prime]:=((2*r)*(D*(lpsPSLList q).length))*s+(D*((2*r')*(lpsPSLList q).length))*s
noncomputable def decodedOperator {q D r r' s:ℕ} [Fact q.Prime] {F:Type} [Field F] [Fintype F]
 (e:Fin s≃F) (t:EncodedFieldTables s) (i:Fin (CheckCount q D r r' s)) (w:List Bool):=
 let rows:=LPSSparseEmitterCodec.rowsOrEmpty (PhysicalCount q D r r') s w
 let word:=lpsEncodedOutputWord e t (rows.getD i.val [])
 match lpsEncodedCheckNumbering.symm i with
 | Sum.inl _=>(registerUnitary (F:=F) (ι':=LiftedProduct.QubitIndex
   (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod q))).conjOperator (shift word)
 | Sum.inr _=>(registerUnitary (F:=F) (ι':=LiftedProduct.QubitIndex
   (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod q))).conjOperator (phase word)
theorem decodedOperator_output {p D r r' s:ℕ} {F:Type} [Field F] [Fintype F]
 (e:Fin s≃F) (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p)
 (h:Matrix (Fin r) (Fin D) F) (h':Matrix (Fin r') (Fin D) F)
 (i:Fin (CheckCount (lpsEffectiveResiduePrimeAt hp hp4 B).q D r r' s)):
 decodedOperator e (encodedFieldTables e) i
 (output hp hp4 B g (encodedFieldTables e) (h.map e.symm) (h'.map e.symm))=
 lpsEncodedOutputOperator e (encodedFieldTables e) (fun j=>lpsEffectiveQuaternionFamilyIndex hp hp4 B (g j))
 (h.map e.symm) (h'.map e.symm) i:=by
 simp only [decodedOperator,LPSSparseEmitterCodec.rowsOrEmpty,decodeTyped_output,Option.getD_some]
 have hi:i.val < (lpsEncodedCheckOutput (encodedFieldTables e)
  (fun j=>lpsEffectiveQuaternionFamilyIndex hp hp4 B (g j)) (h.map e.symm) (h'.map e.symm)).length:=by
  rw [lpsEncodedCheckOutput_length]
  exact i.isLt
 rw [List.getD_eq_getElem _ _ hi]
 rfl
theorem mem_originalFamily_carrier_iff_decodedOutput {p D r r' s:ℕ} {F:Type} [Field F] [Fintype F]
 (e:Fin s≃F) (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p)
 (h:Matrix (Fin r) (Fin D) F) (h':Matrix (Fin r') (Fin D) F)
 (ψ:Semantics.Qudit.QuditRegister (fun _:LiftedProduct.QubitIndex
   (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod (lpsResiduePrimeSequence hp hp4 B).q)=>Fintype.card F)):
 ψ∈(semanticPresentation (fun j=>lpsQuaternionFamilyLabel hp hp4 B (g j)) h h').code.carrier↔
 ∀ i,decodedOperator e (encodedFieldTables e) i
 (output hp hp4 B g (encodedFieldTables e) (h.map e.symm) (h'.map e.symm)) ψ=ψ:=by
 have hc:=mem_originalFamily_carrier_iff_lpsEncodedOutput e hp hp4 B g h h' ψ
 exact hc.trans (by
  constructor
  · intro hall i
    exact (congrArg (fun op=>op ψ) (decodedOperator_output e hp hp4 B g h h' i)).trans (hall i)
  · intro hall i
    exact (congrArg (fun op=>op ψ) (decodedOperator_output e hp hp4 B g h h' i)).symm.trans (hall i))
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
