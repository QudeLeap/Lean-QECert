import QEC.Coding.BitTuring.UnaryQuaternionMatrix
import QEC.Coding.ExpanderCodes.LPSQuaternionRecordMachine
import QEC.Coding.ExpanderCodes.LPSMatrixProductMachine

/-!
# Actual q-only original normalized SL generator matrix emission

For fixed p and an original norm-p quaternion, the complete program accepts only unary q.
It actually computes the original seven-field record and then all four normalized entries,
proving exact equality with the original lpsEffectiveQuaternionSL matrix. All source signs,
coordinates, original residue root and normalization scalar are preserved. Derived record
lengths and actual composition costs yield whole unary-input and true PSL-carrier bounds;
faithful input and standard certificates use this same finite Boolean program.
The complete ordered generator list, original PSL enumeration/indexing, sparse CSS runtime
and strong arithmetic spectral growth remain unproved. This internal closure does not realize
the exact public PK22 main theorem. Bool encodes tapes; the code field remains arbitrary.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSQuaternionMatrixMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open FieldProjection
/-- The actual source record and full arithmetic assembler compose into one q-only program. -/
def machine (p:ℕ) (t:LPSQuaternion) :=
  Composition.machine (LPSQuaternionRecordMachine.machine p t) QuaternionAssembly.machine
/-- Exact original normalized SL matrix row-major canonical output. -/
def output {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :=
  raw (LPSMatrixProductMachine.fields a.q (lpsEffectiveQuaternionSL a t ht).val)
/-- Every emitted matrix entry is the exact original normalized SL construction. -/
theorem output_eq_source {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    QuaternionAssembly.output (LPSDegreeInverseMachine.scalar a) (lpsEffectiveResiduePairIndex a.q)
      (t.d:ZMod a.q).val (t.c:ZMod a.q).val (t.b:ZMod a.q).val (t.a:ZMod a.q).val a.q=
        output a t ht := by
  rw [LPSQuaternionRecordMachine.residue_index_eq_val a]
  unfold LPSDegreeInverseMachine.scalar
  rw [QuaternionAssembly.output_eq_field a.q a.prime.pos]
  simp [output,LPSMatrixProductMachine.fields,lpsEffectiveQuaternionSL,lpsQuaternionMatrix,
    lpsResidueX_zero_of_residuePrime a,sub_eq_add_neg,mul_comm,mul_left_comm,
    add_comm,add_left_comm,mul_add]
/-- Mathematical bound on the actual original seven-field intermediate record. -/
noncomputable def size : Polynomial ℕ := Polynomial.C 7*(Polynomial.X+1)
/-- Whole runtime includes actual q-only initialization, arithmetic and record transfer. -/
noncomputable def time (p:ℕ) (t:LPSQuaternion) : Polynomial ℕ :=
  QuaternionAssembly.time.comp size+Polynomial.C 2*size+LPSQuaternionRecordMachine.time p t+Polynomial.C 2
/-- Complete actual source program emits the original normalized SL matrix from q only. -/
noncomputable def polyExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    EvalsToInTime (TM2.step (machine p t).program) ((machine p t).init (unary a.q))
      (some ((machine p t).halt (output a t ht))) ((time p t).eval (unary a.q).length) := by
  let : NeZero a.q:=⟨a.prime.ne_zero⟩
  have hA:=LPSQuaternionRecordMachine.polyExec a t ht
  have hB:=QuaternionAssembly.polyExec (LPSDegreeInverseMachine.scalar a) (lpsEffectiveResiduePairIndex a.q)
    (t.d:ZMod a.q).val (t.c:ZMod a.q).val (t.b:ZMod a.q).val (t.a:ZMod a.q).val a.q
    a.prime.pos (ZMod.val_lt _)
  rw [output_eq_source a t ht] at hB
  have h:=Composition.executes (LPSQuaternionRecordMachine.machine p t) QuaternionAssembly.machine
    _ _ _ _ _ hA hB
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hL:(LPSQuaternionRecordMachine.record a t).length≤7*(a.q+1) := by
    have hs:LPSDegreeInverseMachine.scalar a<a.q :=ZMod.val_lt _
    have hy:lpsEffectiveResiduePairIndex a.q<a.q := by
      rw [←lpsMinusRoot_pair_index a]
      exact SquareRoot.index_lt _ _ _
    have ha:=ZMod.val_lt (t.a:ZMod a.q)
    have hb:=ZMod.val_lt (t.b:ZMod a.q)
    have hc:=ZMod.val_lt (t.c:ZMod a.q)
    have hd:=ZMod.val_lt (t.d:ZMod a.q)
    simp only [LPSQuaternionRecordMachine.record,stream_length,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil]
    omega
  have hp:QuaternionAssembly.time.eval (LPSQuaternionRecordMachine.record a t).length≤
      QuaternionAssembly.time.eval (7*(a.q+1)) :=
    Composition.polynomial_eval_monotone QuaternionAssembly.time hL
  change QuaternionAssembly.time.eval (LPSQuaternionRecordMachine.record a t).length+
    (2*(LPSQuaternionRecordMachine.record a t).length+2)+
    (LPSQuaternionRecordMachine.time p t).eval (unary a.q).length≤(time p t).eval (unary a.q).length
  simp only [time,size,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,unary_length]
  omega

open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
/-- Actual finite program or proved selector, execution, budget or source certificate. -/
noncomputable def outputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    TM2OutputsInTime (machine p t).toFinTM2 (unary a.q) (some (output a t ht))
      ((time p t).eval (unary a.q).length) :=
  Machine.outputsInTime (machine p t) _ _ _ (polyExec a t ht)
/-- Actual finite program or proved selector, execution, budget or source certificate. -/
noncomputable def computableInPolyTime (p:ℕ) (t:LPSQuaternion) (ht:t.norm=p) :
    TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>output a t ht) where
  tm:=(machine p t).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time p t
  outputsFun:=fun a=>by
    change TM2OutputsInTime (machine p t).toFinTM2 (List.map id (unary a.q))
      (some (List.map id (output a t ht))) ((time p t).eval (unary a.q).length)
    have h:=outputsInTime a t ht
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
open scoped MatrixGroups
/-- Actual finite program or proved selector, execution, budget or source certificate. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    EvalsToInTime (TM2.step (machine p t).program) ((machine p t).init (unary a.q))
      (some ((machine p t).halt (output a t ht))) ((time p t).eval (2*Fintype.card PSL(2,ZMod a.q))) := by
  have h:=polyExec a t ht
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  rw [unary_length]
  exact Composition.polynomial_eval_monotone (time p t) a.q_le_two_mul_card_psl
/-- Actual finite program or proved selector, execution, budget or source certificate. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    TM2OutputsInTime (machine p t).toFinTM2 (unary a.q) (some (output a t ht))
      ((time p t).eval (2*Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime (machine p t) _ _ _ (blockExec a t ht)
/-- Actual finite program or proved selector, execution, budget or source certificate. -/
theorem input_injective (p:ℕ) : Function.Injective (fun a:LPSResiduePrime p=>unary a.q) :=
  lpsResiduePrime_unary_injective p

end QEC.Coding.TannerLiftedProduct.LPSQuaternionMatrixMachine
