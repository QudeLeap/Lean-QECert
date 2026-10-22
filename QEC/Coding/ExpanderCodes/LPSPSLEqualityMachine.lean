import QEC.Coding.BitTuring.UnaryPSLComparison
import QEC.Coding.ExpanderCodes.LPSMatrixProductMachine

/-!
# Actual original PSL quotient-equality predicate

The fixed actual machine reads both SL representatives in original row-major order and q,
computes its own scalar negatives/comparisons and returns exactly the original PSL quotient
equality under lpsPSLDecidableEq. Prove whole clean execution, faithful pair input, standard
Mathlib certificates and runtime polynomial in the true original PSL carrier cardinality.
Original last-occurrence deduplication and ordered index lookup are the immediate consumers;
their complete programs remain obligations. No alternative ordering or sign representative is
introduced. Whole sparse CSS runtime and strong arithmetic spectral growth remain unproved.
The exact arbitrary-field public PK22 theorem remains unregistered and unproved. Bool is the
tape alphabet; complexity here is unary-input polynomial time.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSPSLEqualityMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def input (q:ℕ) (A B:SL(2,ZMod q)) : List Bool :=
  stream (LPSMatrixProductMachine.fields q A.val++LPSMatrixProductMachine.fields q B.val++[q])
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 def output (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) : List Bool :=
  letI:=lpsPSLDecidableEq q
  [decide ((QuotientGroup.mk A:PSL(2,ZMod q))=QuotientGroup.mk B)]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem entries_eq (q:ℕ) (A B:SL(2,ZMod q)) :
    A=B ↔ A.val 0 0=B.val 0 0 ∧ A.val 0 1=B.val 0 1 ∧
      A.val 1 0=B.val 1 0 ∧ A.val 1 1=B.val 1 1 :=by
  constructor
  · rintro rfl;simp
  · rintro ⟨h00,h01,h10,h11⟩
    apply Subtype.ext
    ext i j;fin_cases i <;> fin_cases j <;> assumption
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem result_eq_source (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) :
    [QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.result (A.val 0 0).val (A.val 0 1).val (A.val 1 0).val (A.val 1 1).val
      (B.val 0 0).val (B.val 0 1).val (B.val 1 0).val (B.val 1 1).val q]=output q A B :=by
  let : NeZero q:=⟨(Fact.out:q.Prime).ne_zero⟩
  let :=lpsPSLDecidableEq q
  have hn (z:ZMod q):ModularNegation.output z.val q=(-z).val :=by
    rw [ModularNegation.output_eq_neg _ _ (Fact.out:q.Prime).pos (ZMod.val_lt _),ZMod.natCast_zmod_val]
  simp only [QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.result,hn,Function.Injective.eq_iff (ZMod.val_injective q),
    ←Bool.decide_and,←Bool.decide_or,output]
  simp only [List.cons.injEq, and_true]
  apply Bool.decide_congr
  rw [lpsPSLMk_eq_iff,entries_eq q A B,entries_eq q (-A) B]
  simp [and_comm,or_comm]
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 noncomputable def exec (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) :
    EvalsToInTime (TM2.step QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.program)
      (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.init (input q A B))
      (some (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.halt (output q A B)))
      (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time.eval (input q A B).length) :=by
  let : NeZero q:=⟨(Fact.out:q.Prime).ne_zero⟩
  have h:=QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.polyExec (A.val 0 0).val (A.val 0 1).val (A.val 1 0).val (A.val 1 1).val
    (B.val 0 0).val (B.val 0 1).val (B.val 1 0).val (B.val 1 1).val q
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
  rw [result_eq_source q A B] at h
  simpa only [input,LPSMatrixProductMachine.fields,List.cons_append,List.nil_append] using h
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 theorem input_injective (q:ℕ) (hq:0<q) : Function.Injective (fun x:SL(2,ZMod q)×SL(2,ZMod q)=>input q x.1 x.2) :=by
  intro x y hh
  have he:=stream_injective hh
  simp only [LPSMatrixProductMachine.fields,List.cons_append,List.nil_append,List.cons.injEq] at he
  rcases he with ⟨h00,h01,h10,h11,h20,h21,h30,h31,_⟩
  apply Prod.ext
  · apply Subtype.ext
    exact LPSMatrixProductMachine.fields_injective q hq (by simp [LPSMatrixProductMachine.fields,h00,h01,h10,h11])
  · apply Subtype.ext
    exact LPSMatrixProductMachine.fields_injective q hq (by simp [LPSMatrixProductMachine.fields,h20,h21,h30,h31])
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 noncomputable def outputsInTime (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) :
    TM2OutputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.toFinTM2 (input q A B)
      (some (output q A B)) (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time.eval (input q A B).length) :=
  Machine.outputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine _ _ _ (exec q A B)
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 noncomputable def computableInPolyTime (q:ℕ) [Fact q.Prime] :
    TM2ComputableInPolyTime (fun x:SL(2,ZMod q)×SL(2,ZMod q)=>input q x.1 x.2)
      id (fun x=>output q x.1 x.2) where
  tm:=QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time
  outputsFun:=fun x=>by
    change TM2OutputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.toFinTM2
      (List.map id (input q x.1 x.2)) (some (List.map id (output q x.1 x.2)))
      (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time.eval (input q x.1 x.2).length)
    have h:=outputsInTime q x.1 x.2
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 noncomputable def carrierTime : Polynomial ℕ := QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time.comp
  (Polynomial.C 18*Polynomial.X+Polynomial.C 9)
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 noncomputable def carrierExec {p:ℕ} (a:LPSResiduePrime p) (A B:SL(2,ZMod a.q)) :
    EvalsToInTime (TM2.step QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.program)
      (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.init (input a.q A B))
      (some (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.halt (output a.q A B)))
      (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))) :=by
  have h:=exec a.q A B
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  let : NeZero a.q:=⟨a.prime.pos.ne'⟩
  have hbound:(input a.q A B).length≤18*Fintype.card PSL(2,ZMod a.q)+9 :=by
    have hq:=a.q_le_two_mul_card_psl
    have h00:=ZMod.val_lt (A.val 0 0)
    have h01:=ZMod.val_lt (A.val 0 1)
    have h10:=ZMod.val_lt (A.val 1 0)
    have h11:=ZMod.val_lt (A.val 1 1)
    have h20:=ZMod.val_lt (B.val 0 0)
    have h21:=ZMod.val_lt (B.val 0 1)
    have h30:=ZMod.val_lt (B.val 1 0)
    have h31:=ZMod.val_lt (B.val 1 1)
    simp only [input,LPSMatrixProductMachine.fields,List.cons_append,List.nil_append,
      stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  simp only [carrierTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  exact Composition.polynomial_eval_monotone QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time hbound
/-- Actual finite instructions or proved execution invariant, whole budget or original source certificate. -/
 noncomputable def carrierOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (A B:SL(2,ZMod a.q)) :
    TM2OutputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.toFinTM2 (input a.q A B)
      (some (output a.q A B)) (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine _ _ _ (carrierExec a A B)
end QEC.Coding.TannerLiftedProduct.LPSPSLEqualityMachine
