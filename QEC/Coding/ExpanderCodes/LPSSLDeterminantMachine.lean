import QEC.Coding.BitTuring.UnaryDeterminantPredicate
import QEC.Coding.ExpanderCodes.LPSMatrixProductMachine

/-!
# Actual original SL determinant-one candidate criterion

For original canonical row-major entries and q>1, the fixed actual determinant program emits
exactly the original lpsEntryMatrix determinant-one condition and lpsSLMatrixCandidate.isSome.
This includes every prime source modulus and characteristic two, without requiring a supplied
determinant proof or candidate result. Prove complete clean execution, faithful source input,
standard Mathlib certificates and a quadratic budget in the true original PSL cardinality.
Immediate consumers are original lpsSLList filtering and original lpsPSLList enumeration before
last-occurrence deduplication. Their complete loops, original ordered PSL dedup/index, whole
sparse CSS runtime and strong arithmetic spectral growth remain obligations. No original
ordering or representative is replaced. The exact arbitrary-field public PK22 theorem remains
unproved and unregistered. Bool is the tape alphabet; code field remains arbitrary.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSSLDeterminantMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
open QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 theorem predicate_eq_source (q:ℕ) (hq:1<q) (a b c d:Fin q) :
    decide (result a.val b.val c.val d.val q=1)=
      decide ((QEC.Coding.TannerLiftedProduct.lpsEntryMatrix q a b c d).det=1) :=by
  let : NeZero q:=⟨by omega⟩
  have hv:=result_eq_det q (by omega) (a.val:ZMod q) (b.val:ZMod q) (c.val:ZMod q) (d.val:ZMod q)
  simp only [ZMod.val_natCast_of_lt a.isLt,ZMod.val_natCast_of_lt b.isLt,
    ZMod.val_natCast_of_lt c.isLt,ZMod.val_natCast_of_lt d.isLt] at hv
  rw [hv]
  apply Bool.decide_congr
  change (QEC.Coding.TannerLiftedProduct.lpsEntryMatrix q a b c d).det.val=1 ↔ _
  have hh:(QEC.Coding.TannerLiftedProduct.lpsEntryMatrix q a b c d).det.val=(1:ZMod q).val ↔
      (QEC.Coding.TannerLiftedProduct.lpsEntryMatrix q a b c d).det=1 :=(ZMod.val_injective q).eq_iff
  simpa only [ZMod.val_one'' (by omega:q≠1)] using hh
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 noncomputable def sourceExec (q:ℕ) (hq:1<q) (a b c d:Fin q) :
    EvalsToInTime (TM2.step predicateMachine.program)
      (predicateMachine.init (stream [a.val,b.val,c.val,d.val,q]))
      (some (predicateMachine.halt [decide ((QEC.Coding.TannerLiftedProduct.lpsEntryMatrix q a b c d).det=1)]))
      (predicateTime.eval (stream [a.val,b.val,c.val,d.val,q]).length) :=by
  have h:=predicatePolyExec a.val b.val c.val d.val q (by omega)
  rw [predicate_eq_source q hq a b c d] at h
  exact h
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 theorem predicate_eq_candidate (q:ℕ) (hq:1<q) (a b c d:Fin q) :
    decide (result a.val b.val c.val d.val q=1)=
      (QEC.Coding.TannerLiftedProduct.lpsSLMatrixCandidate q a b c d).isSome :=by
  rw [predicate_eq_source q hq a b c d]
  unfold QEC.Coding.TannerLiftedProduct.lpsSLMatrixCandidate
  split_ifs
  all_goals simp_all
  all_goals rfl
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 def sourceInput (q:ℕ) (x:Fin q×Fin q×Fin q×Fin q):=stream [x.1.val,x.2.1.val,x.2.2.1.val,x.2.2.2.val,q]
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 def sourceOutput (q:ℕ) (x:Fin q×Fin q×Fin q×Fin q):=
    [decide ((QEC.Coding.TannerLiftedProduct.lpsEntryMatrix q x.1 x.2.1 x.2.2.1 x.2.2.2).det=1)]
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 theorem sourceInput_injective (q:ℕ):Function.Injective (sourceInput q):=by
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ hh
  have he:=stream_injective hh
  simp only [List.cons.injEq] at he
  rcases he with ⟨ha,hb,hc,hd,_⟩
  apply Prod.ext
  · exact Fin.ext ha
  · apply Prod.ext
    · exact Fin.ext hb
    · apply Prod.ext
      · exact Fin.ext hc
      · exact Fin.ext hd
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 noncomputable def sourceOutputsInTime (q:ℕ) (hq:1<q) (x:Fin q×Fin q×Fin q×Fin q):
    TM2OutputsInTime predicateMachine.toFinTM2 (sourceInput q x) (some (sourceOutput q x))
      (predicateTime.eval (sourceInput q x).length):=
  Machine.outputsInTime predicateMachine _ _ _ (sourceExec q hq x.1 x.2.1 x.2.2.1 x.2.2.2)
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 noncomputable def sourceComputableInPolyTime (q:ℕ) (hq:1<q):
    TM2ComputableInPolyTime (sourceInput q) id (sourceOutput q) where
  tm:=predicateMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=predicateTime
  outputsFun:=fun x=>by
    change TM2OutputsInTime predicateMachine.toFinTM2 (List.map id (sourceInput q x))
      (some (List.map id (sourceOutput q x))) (predicateTime.eval (sourceInput q x).length)
    have h:=sourceOutputsInTime q hq x
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
 open QEC.Coding.TannerLiftedProduct
 open scoped MatrixGroups
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 noncomputable def carrierTime:Polynomial ℕ:=predicateTime.comp (Polynomial.C 10*Polynomial.X+Polynomial.C 5)
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 noncomputable def carrierExec {p:ℕ} (a:LPSResiduePrime p) (x:Fin a.q×Fin a.q×Fin a.q×Fin a.q):
    EvalsToInTime (TM2.step predicateMachine.program) (predicateMachine.init (sourceInput a.q x))
      (some (predicateMachine.halt (sourceOutput a.q x))) (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))) :=by
  have h:=sourceExec a.q a.prime.one_lt x.1 x.2.1 x.2.2.1 x.2.2.2
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hbound:(sourceInput a.q x).length≤10*Fintype.card PSL(2,ZMod a.q)+5:=by
    have hq:=a.q_le_two_mul_card_psl
    have h0:=x.1.isLt
    have h1:=x.2.1.isLt
    have h2:=x.2.2.1.isLt
    have h3:=x.2.2.2.isLt
    simp only [sourceInput,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  simp only [carrierTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  exact Composition.polynomial_eval_monotone predicateTime hbound
/-- Actual finite instructions or proved determinant invariant, whole budget or source certificate. -/
 noncomputable def carrierOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (x:Fin a.q×Fin a.q×Fin a.q×Fin a.q):
    TM2OutputsInTime predicateMachine.toFinTM2 (sourceInput a.q x) (some (sourceOutput a.q x))
      (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))):=
  Machine.outputsInTime predicateMachine _ _ _ (carrierExec a x)
end QEC.Coding.TannerLiftedProduct.LPSSLDeterminantMachine
