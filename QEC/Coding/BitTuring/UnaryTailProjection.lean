import QEC.Coding.BitTuring.SuffixJoin
import QEC.Coding.BitTuring.UnaryMatrixListQuery

/-!
# Actual unary prefix projection with retained suffix

Compose the actual fixed-mask field projection and suffix-join compiler. Exact stream/raw identities and polynomial bounds retain arbitrary later bits instead of discarding the remaining source rows.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.TailProjection
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
/-- Actual masked-prefix projection, preserved suffix encoding or complete polynomial execution. -/
def machine:=QEC.Coding.BitTuring.SuffixJoin.machine (FieldProjection.machine n keep)
/-- Actual masked-prefix projection, preserved suffix encoding or complete polynomial execution. -/
noncomputable def time:Polynomial ℕ:=Polynomial.C 6*(Polynomial.X+1)
/-- Actual masked-prefix projection, preserved suffix encoding or complete polynomial execution. -/
def exec (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool):
 EvalsToInTime (TM2.step (machine n keep).program) ((machine n keep).init (stream xs++s))
  (some ((machine n keep).halt (raw (fields n keep 0 xs)++false::s)))
  (steps n keep xs+2*(s.length+(raw (fields n keep 0 xs)).length)+4):=
 QEC.Coding.BitTuring.SuffixJoin.exec (FieldProjection.machine n keep) (by change (0:Fin 3)≠2;decide) _ _ _ _
  (PrefixProjection.partialExec n keep xs hx s)
/-- Actual masked-prefix projection, preserved suffix encoding or complete polynomial execution. -/
noncomputable def polyExec (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool):
 EvalsToInTime (TM2.step (machine n keep).program) ((machine n keep).init (stream xs++s))
  (some ((machine n keep).halt (raw (fields n keep 0 xs)++false::s)))
  (time.eval (stream xs++s).length):=by
 have h:=exec n keep xs hx s
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hs:=FieldProjection.steps_le n keep xs
 have hr:=FieldProjection.raw_length_le (fields n keep 0 xs)
 have hf:=FieldProjection.fields_stream_length_le n keep 0 xs
 simp only [time,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,
  Polynomial.eval_one,List.length_append]
 omega
/-- Actual masked-prefix projection, preserved suffix encoding or complete polynomial execution. -/
noncomputable def streamExec (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool)
 (hne:fields n keep 0 xs≠[]):
 EvalsToInTime (TM2.step (machine n keep).program) ((machine n keep).init (stream xs++s))
  (some ((machine n keep).halt (stream (fields n keep 0 xs)++s)))
  (time.eval (stream xs++s).length):=by
 have h:=polyExec n keep xs hx s
 have he:raw (fields n keep 0 xs)++false::s=stream (fields n keep 0 xs)++s:=by
  rw [←MatrixListQuery.delimiter_raw _ hne]
  simp only [List.append_assoc,List.singleton_append]
 rw [he] at h
 exact h
/-- Actual masked-prefix projection, preserved suffix encoding or complete polynomial execution. -/
noncomputable def computableInPolyTime:
 TM2ComputableInPolyTime (PrefixProjection.input n) id
  (fun x:PrefixProjection.Input n=>raw (fields n keep 0 x.1.val)++false::x.2) where
 tm:=(machine n keep).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time
 outputsFun:=fun x=>by
  change TM2OutputsInTime (machine n keep).toFinTM2 (List.map id (PrefixProjection.input n x))
    (some (List.map id (raw (fields n keep 0 x.1.val)++false::x.2)))
    (time.eval (PrefixProjection.input n x).length)
  have h:=Machine.outputsInTime (machine n keep) _ _ _ (polyExec n keep x.1.val x.1.property x.2)
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id,PrefixProjection.input] using h
/-- Actual masked-prefix projection, preserved suffix encoding or complete polynomial execution. -/
noncomputable def identityExec (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool):
 EvalsToInTime (TM2.step (machine n (PrefixProjection.allMask n)).program)
  ((machine n (PrefixProjection.allMask n)).init (stream xs++s))
  (some ((machine n (PrefixProjection.allMask n)).halt (stream xs++s)))
  (time.eval (stream xs++s).length):=by
 have hn:fields n (PrefixProjection.allMask n) 0 xs≠[]:=by
  rw [PrefixProjection.fields_all]
  intro h;subst xs;simp at hx
 have h:=streamExec n (PrefixProjection.allMask n) xs hx s hn
 rw [PrefixProjection.fields_all] at h
 exact h
end QEC.Coding.BitTuring.UnaryArithmetic.TailProjection
