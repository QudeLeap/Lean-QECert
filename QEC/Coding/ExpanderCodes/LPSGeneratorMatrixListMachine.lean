import QEC.Coding.BitTuring.UnaryMatrixListQuery
import QEC.Coding.ExpanderCodes.LPSQuaternionMatrixMachine
import QEC.Coding.ExpanderCodes.JacobiFourSquareCount
import Mathlib.Data.List.OfFn

/-!
# Actual complete original ordered LPS generator-matrix list

A fixed finite direction list determines actual q-only matrix programs. Tail-first execution
and actual retained four-entry queries emit every original normalized SL matrix in that same
direction order and row-major order; a final real projection discards retained q. Every actual
stage, retention and transfer has a derived whole unary polynomial budget, faithful input,
standard Mathlib certificate and true original PSL-carrier bound.
The exact original Fin(p+1) equivalence from proved Jacobi count covers all original directions
once and keeps the local-code matrix coordinates. Each emitted SL quotient is the original
family label. No varying source value is compiled into instructions; q alone is tape input.
Original ordered PSL enumeration/index lookup, complete sparse CSS execution/runtime and
strong arithmetic spectral growth remain unproved. This internal closure does not realize
the exact public PK22 theorem. Bool is the tape alphabet; code field remains arbitrary.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection MatrixListQuery
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def matrixFields {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):List ℕ :=
   LPSMatrixProductMachine.fields a.q
     (lpsEffectiveQuaternionSL a t.val (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.property)).val
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem matrixFields_length {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p) :
    (matrixFields a t).length=4 :=by simp [matrixFields,LPSMatrixProductMachine.fields]
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem matrixFields_bound {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p) :
    ∀x∈matrixFields a t,x<a.q :=by
  let : NeZero a.q:=⟨a.prime.ne_zero⟩
  simp only [matrixFields,LPSMatrixProductMachine.fields,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with h|h|h|h <;> subst x <;> exact ZMod.val_lt _
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def listFields {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) :=
   ts.flatMap (matrixFields a)
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem listFields_length {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) :
    (listFields a ts).length=4*ts.length :=by
  induction ts with
  | nil=>simp [listFields]
  | cons t ts ih=>
    change (matrixFields a t++listFields a ts).length=_
    rw [List.length_append,matrixFields_length,ih,List.length_cons]
    omega
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem listFields_bound {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) :
    ∀x∈listFields a ts,x<a.q :=by
  intro x hx
  simp only [listFields,List.mem_flatMap] at hx
  rcases hx with ⟨t,ht,hx⟩
  exact matrixFields_bound a t x hx
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem record_length {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) :
    (stream (listFields a ts++[a.q])).length≤(4*ts.length+1)*(a.q+1) :=by
  have h:=stream_length_bound a.q (listFields a ts) (listFields_bound a ts)
  rw [stream_append]
  simp only [List.length_append,stream,unary_length,List.length_cons,
    List.length_nil,listFields_length] at h ⊢
  nlinarith

/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def collector {p:ℕ} : List (LPSGeneratorIndex p)→Machine
  | []=>identityMachine
  | t::ts=>Composition.machine (collector ts)
      (queryMachine (4*ts.length) (LPSQuaternionMatrixMachine.machine p t.val))
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def collectorTime {p:ℕ} : List (LPSGeneratorIndex p)→Polynomial ℕ
  | []=>Polynomial.C 8*(Polynomial.X+1)
  | t::ts=>collectorTime ts+LPSQuaternionMatrixMachine.time p t.val+
      Polynomial.C 52*(Polynomial.C (4*ts.length+1)*(Polynomial.X+1)+1)
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def collectorExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) :
    EvalsToInTime (TM2.step (collector ts).program) ((collector ts).init (stream [a.q]))
      (some ((collector ts).halt (stream (listFields a ts++[a.q]))))
      ((collectorTime ts).eval a.q) :=by
  induction ts with
  | nil=>
    have h:=identityExec (stream [a.q])
    refine {h with steps_le_m:=h.steps_le_m.trans ?_}
    simp only [collectorTime,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,stream,List.length_append,
      List.length_cons,List.length_nil,unary_length]
    omega
  | cons t ts ih=>
    have hm:=LPSQuaternionMatrixMachine.polyExec a t.val
      (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.property)
    rw [unary_length] at hm
    change EvalsToInTime (TM2.step (LPSQuaternionMatrixMachine.machine p t.val).program)
      ((LPSQuaternionMatrixMachine.machine p t.val).init (unary a.q))
      (some ((LPSQuaternionMatrixMachine.machine p t.val).halt (raw (matrixFields a t))))
      ((LPSQuaternionMatrixMachine.time p t.val).eval a.q) at hm
    have hq:=queryExec (4*ts.length) (LPSQuaternionMatrixMachine.machine p t.val)
      (LPSQuaternionMatrixMachine.time p t.val) (listFields a ts) (matrixFields a t) a.q
      (listFields_length a ts) (matrixFields_length a t) (matrixFields_bound a t) hm
    have h:=Composition.executes (collector ts)
      (queryMachine (4*ts.length) (LPSQuaternionMatrixMachine.machine p t.val))
      _ _ _ _ _ ih hq
    refine {h with steps_le_m:=h.steps_le_m.trans ?_}
    have hL:=record_length a ts
    simp only [collectorTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def machine {p:ℕ} (ts:List (LPSGeneratorIndex p)) := Composition.machine BitDelimiter.machine
   (Composition.machine (collector ts) (FieldProjection.machine (4*ts.length) (prefixMask (4*ts.length))))
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def output {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) := raw (listFields a ts)
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def time {p:ℕ} (ts:List (LPSGeneratorIndex p)) : Polynomial ℕ :=
   collectorTime ts+Polynomial.C 10*(Polynomial.C (4*ts.length+1)*(Polynomial.X+1)+1)
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def polyExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) :
    EvalsToInTime (TM2.step (machine ts).program) ((machine ts).init (unary a.q))
      (some ((machine ts).halt (output a ts))) ((time ts).eval a.q) :=by
  have hd:=BitDelimiter.exec (unary a.q)
  rw [show unary a.q++[false]=stream [a.q] by simp [stream]] at hd
  have hc:=collectorExec a ts
  have hp:=FieldProjection.polyExec (4*ts.length) (prefixMask (4*ts.length))
    (listFields a ts++[a.q]) (by simp [listFields_length])
  rw [selectPrefix (4*ts.length) 0 (listFields a ts) a.q (by simp [listFields_length])] at hp
  have ht:=Composition.executes (collector ts)
    (FieldProjection.machine (4*ts.length) (prefixMask (4*ts.length))) _ _ _ _ _ hc hp
  have h:=Composition.executes BitDelimiter.machine
    (Composition.machine (collector ts) (FieldProjection.machine (4*ts.length) (prefixMask (4*ts.length))))
    _ _ _ _ _ hd ht
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hL:=record_length a ts
  simp only [time,FieldProjection.time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,stream,List.length_append,List.length_cons,List.length_nil,
    unary_length]
  nlinarith
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def outputsInTime {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) :
    TM2OutputsInTime (machine ts).toFinTM2 (unary a.q) (some (output a ts)) ((time ts).eval a.q) :=
   Machine.outputsInTime (machine ts) _ _ _ (polyExec a ts)
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def computableInPolyTime {p:ℕ} (ts:List (LPSGeneratorIndex p)) :
    TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>output a ts) where
  tm:=(machine ts).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time ts
  outputsFun:=fun a=>by
    change TM2OutputsInTime (machine ts).toFinTM2 (List.map id (unary a.q))
      (some (List.map id (output a ts))) ((time ts).eval (unary a.q).length)
    have h:=outputsInTime a ts
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,unary_length] using h
 open scoped MatrixGroups
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) :
    EvalsToInTime (TM2.step (machine ts).program) ((machine ts).init (unary a.q))
      (some ((machine ts).halt (output a ts))) ((time ts).eval (2*Fintype.card PSL(2,ZMod a.q))) :=by
  have h:=polyExec a ts
  exact {h with steps_le_m:=h.steps_le_m.trans (Composition.polynomial_eval_monotone
    (time ts) a.q_le_two_mul_card_psl)}
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) :
    TM2OutputsInTime (machine ts).toFinTM2 (unary a.q) (some (output a ts))
      ((time ts).eval (2*Fintype.card PSL(2,ZMod a.q))) :=
   Machine.outputsInTime (machine ts) _ _ _ (blockExec a ts)
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem input_injective (p:ℕ) : Function.Injective (fun a:LPSResiduePrime p=>unary a.q) :=
   lpsResiduePrime_unary_injective p

/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem orderedFields {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) :
    listFields a (List.ofFn g)=(List.ofFn (fun j=>matrixFields a (g j))).flatten :=by
  simp [listFields,List.flatMap_def,List.map_ofFn,Function.comp_def]
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def generatorSL {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p) : SL(2,ZMod a.q) :=
   lpsEffectiveQuaternionSL a t.val (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.property)
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem generatorSL_decode {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p) :
    (QuotientGroup.mk (generatorSL a t):PSL(2,ZMod a.q))=lpsQuaternionLabel a t :=by
  exact lpsEffectiveQuaternionPSL_eq a t.val _
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def sourceDirections {p:ℕ} (hp:p.Prime) (hp4:p%4=1) : List (LPSGeneratorIndex p) :=
   List.ofFn (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4))
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem sourceDirections_length {p:ℕ} (hp:p.Prime) (hp4:p%4=1) :
    (sourceDirections hp hp4).length=p+1 :=by simp [sourceDirections]
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem sourceDirections_nodup {p:ℕ} (hp:p.Prime) (hp4:p%4=1) :
    (sourceDirections hp hp4).Nodup :=by
  apply List.nodup_ofFn_ofInjective
  exact (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4)).injective
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem sourceDirections_complete {p:ℕ} (hp:p.Prime) (hp4:p%4=1) (t:LPSGeneratorIndex p) :
    t∈sourceDirections hp hp4 :=by
  simp only [sourceDirections,List.mem_ofFn]
  exact (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4)).surjective t
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem sourceFields_length {p:ℕ} (a:LPSResiduePrime p) :
    (listFields a (sourceDirections a.degreePrime a.degreeModFour)).length=4*(p+1) :=by
  rw [listFields_length,sourceDirections_length]
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def sourceOutput {p:ℕ} (a:LPSResiduePrime p) : List Bool :=
   raw ((List.ofFn (fun j=>LPSMatrixProductMachine.fields a.q
     (generatorSL a (lpsFinGeneratorEquiv
       (card_lpsQuaternionShell_eq_prime_add_one a.degreePrime a.degreeModFour) j)).val)).flatten)
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem output_eq_source {p:ℕ} (a:LPSResiduePrime p) :
    output a (sourceDirections a.degreePrime a.degreeModFour)=sourceOutput a :=by
  simp only [output,sourceOutput,sourceDirections,orderedFields,generatorSL,matrixFields]
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def sourceExec {p:ℕ} (a:LPSResiduePrime p) :
    EvalsToInTime (TM2.step (machine (sourceDirections a.degreePrime a.degreeModFour)).program)
      ((machine (sourceDirections a.degreePrime a.degreeModFour)).init (unary a.q))
      (some ((machine (sourceDirections a.degreePrime a.degreeModFour)).halt (sourceOutput a)))
      ((time (sourceDirections a.degreePrime a.degreeModFour)).eval a.q) :=by
  have h:=polyExec a (sourceDirections a.degreePrime a.degreeModFour)
  rw [output_eq_source] at h
  exact h
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem sourceDirection_decode {p:ℕ} (hp:p.Prime) (hp4:p%4=1) (n:ℕ) (j:Fin (p+1)) :
    (QuotientGroup.mk (generatorSL (lpsEffectiveResiduePrimeAt hp hp4 n)
      (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4) j)):
      PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 n).q))=
        lpsFinQuaternionFamilyLabel hp hp4 (card_lpsQuaternionShell_eq_prime_add_one hp hp4) n j :=by
  rw [generatorSL_decode]
  rfl
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def sourceComputableInPolyTime {p:ℕ} (hp:p.Prime) (hp4:p%4=1) :=
   computableInPolyTime (sourceDirections hp hp4)
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def sourceBlockExec {p:ℕ} (a:LPSResiduePrime p) :
    EvalsToInTime (TM2.step (machine (sourceDirections a.degreePrime a.degreeModFour)).program)
      ((machine (sourceDirections a.degreePrime a.degreeModFour)).init (unary a.q))
      (some ((machine (sourceDirections a.degreePrime a.degreeModFour)).halt (sourceOutput a)))
      ((time (sourceDirections a.degreePrime a.degreeModFour)).eval (2*Fintype.card PSL(2,ZMod a.q))) :=by
  have h:=blockExec a (sourceDirections a.degreePrime a.degreeModFour)
  rw [output_eq_source] at h
  exact h
end QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
