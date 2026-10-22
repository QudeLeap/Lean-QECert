import QEC.Coding.BitTuring.UnaryModularAdjugate
import QEC.Coding.ExpanderCodes.LPSMatrixProductMachine

/-!
# Actual original SL matrix inverse emission

The complete actual Boolean adjugate emitter computes all four entries of the original SL
inverse, using Mathlib's exact determinant-one inverse formula and actual canonical negations.
Original canonical input lengths and q<=2*cardPSL yield a true PSL-carrier linear polynomial.
No inverse answer or cost field is supplied. Original PSL indexing, normalization-matrix and
sparse CSS emission/runtime, and strong arithmetic growth remain unproved; this internal
closure does not realize the exact public PK22 main theorem.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
open scoped MatrixGroups

/-- Faithful encoding of the original operands and modulus. -/
def input (q:ℕ) (A:SL(2,ZMod q)) :=
  FieldProjection.stream (LPSMatrixProductMachine.fields q A.val++[q])
/-- Mathematical specification of the emitted result; never a program callback. -/
def output (q:ℕ) (A:SL(2,ZMod q)) :=
  FieldProjection.raw (LPSMatrixProductMachine.fields q (A⁻¹).val)

/-- Exact original SL inverse formula in canonical row-major fields. -/
theorem inverse_fields (q:ℕ) (A:SL(2,ZMod q)) :
    LPSMatrixProductMachine.fields q (A⁻¹).val=
      [(A.val 1 1).val,(-(A.val 0 1)).val,(-(A.val 1 0)).val,(A.val 0 0).val] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [LPSMatrixProductMachine.fields]

/-- Whole actual clean execution at the derived input-length polynomial budget. -/
noncomputable def polyExec (q:ℕ) (hq:0<q) (A:SL(2,ZMod q)) :
    EvalsToInTime (TM2.step ModularAdjugate.inverseMachine.program) (ModularAdjugate.inverseMachine.init (input q A))
      (some (ModularAdjugate.inverseMachine.halt (output q A)))
      (ModularAdjugate.time.eval (input q A).length) := by
  let : NeZero q:=⟨hq.ne'⟩
  have h:=ModularAdjugate.polyExec (A.val 0 0).val (A.val 0 1).val (A.val 1 0).val (A.val 1 1).val
    q hq (ZMod.val_lt _) (ZMod.val_lt _)
  rw [ModularNegation.output_eq_neg _ _ hq (ZMod.val_lt _),
    ModularNegation.output_eq_neg _ _ hq (ZMod.val_lt _),ZMod.natCast_zmod_val,ZMod.natCast_zmod_val] at h
  rw [output,inverse_fields]
  simpa only [input,LPSMatrixProductMachine.fields,List.cons_append,List.nil_append] using h

/-- Standard Mathlib output certificate from the whole actual program. -/
noncomputable def outputsInTime (q:ℕ) (hq:0<q) (A:SL(2,ZMod q)) :
    TM2OutputsInTime ModularAdjugate.inverseMachine.toFinTM2 (input q A) (some (output q A))
      (ModularAdjugate.time.eval (input q A).length) :=
  Machine.outputsInTime ModularAdjugate.inverseMachine _ _ _ (polyExec q hq A)

/-- Actual linear source runtime polynomial in the true PSL carrier cardinality. -/
noncomputable def carrierTime : Polynomial ℕ := ModularAdjugate.time.comp
  (Polynomial.C 10*Polynomial.X+Polynomial.C 5)
/-- Whole original SL inverse program at its derived true carrier budget. -/
noncomputable def carrierExec {p:ℕ} (a:LPSResiduePrime p) (A:SL(2,ZMod a.q)) :
    EvalsToInTime (TM2.step ModularAdjugate.inverseMachine.program) (ModularAdjugate.inverseMachine.init (input a.q A))
      (some (ModularAdjugate.inverseMachine.halt (output a.q A)))
      (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))) := by
  have h:=polyExec a.q a.prime.pos A
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  let : NeZero a.q:=⟨a.prime.pos.ne'⟩
  have hbound:(input a.q A).length≤10*Fintype.card PSL(2,ZMod a.q)+5 := by
    have hq:=a.q_le_two_mul_card_psl
    have h00:=ZMod.val_lt (A.val 0 0)
    have h01:=ZMod.val_lt (A.val 0 1)
    have h10:=ZMod.val_lt (A.val 1 0)
    have h11:=ZMod.val_lt (A.val 1 1)
    simp only [input,LPSMatrixProductMachine.fields,List.cons_append,List.nil_append,
      FieldProjection.stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  simp only [carrierTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  exact Composition.polynomial_eval_monotone ModularAdjugate.time hbound

/-- Standard actual original SL inverse output at the true carrier budget. -/
noncomputable def carrierOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (A:SL(2,ZMod a.q)) :
    TM2OutputsInTime ModularAdjugate.inverseMachine.toFinTM2 (input a.q A) (some (output a.q A))
      (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime ModularAdjugate.inverseMachine _ _ _ (carrierExec a A)

end QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine

namespace QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing
open scoped MatrixGroups

/-- The source encoding distinguishes every original SL matrix at a positive modulus. -/
theorem input_injective (q:ℕ) (hq:0<q) : Function.Injective (input q) := by
  intro A B h
  have he:=FieldProjection.stream_injective h
  have hm:=LPSMatrixProductMachine.fields_injective q hq (List.append_cancel_right he)
  exact Subtype.ext hm

/-- Standard polynomial-time certificate for the exact original SL inverse function. -/
noncomputable def computableInPolyTime (q:ℕ) (hq:0<q) :
    TM2ComputableInPolyTime (input q) id (output q) where
  tm:=ModularAdjugate.inverseMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=ModularAdjugate.time
  outputsFun:=fun A=>by
    change TM2OutputsInTime ModularAdjugate.inverseMachine.toFinTM2 (List.map id (input q A))
      (some (List.map id (output q A))) (ModularAdjugate.time.eval (input q A).length)
    have h:=outputsInTime q hq A
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
end QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine
