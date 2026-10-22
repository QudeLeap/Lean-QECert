import QEC.Coding.BitTuring.UnaryPrefixProjection
import QEC.Coding.BitTuring.UnaryMatrixListQuery

/-!
# Actual retained predicate query on a fixed unary header and dynamic suffix

Compose the real prefix scanner/drain, real Boolean delimiter, actual predicate body and actual
input-retention compiler. An independently proved execution of that body on the header gives
complete clean execution on header plus arbitrary suffix, returning its own flag and exact
original input. The whole budget p(input_length)+20*(input_length+1) includes every input scan,
tail drain, delimiter, transfer, body and retention instruction. No expected flag or cost is
machine input/control. Original SL filtering and PSL equality on dynamic contexts instantiate
the wrapper with genuine independently proved source-body executions.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (A:Machine)
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
def queryMachine:=RetainedInput.machine
  (Composition.machine (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.prefixMachine n (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.allMask n))
    (Composition.machine BitDelimiter.machine A))
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
noncomputable def time (p:Polynomial ℕ):Polynomial ℕ:=p+Polynomial.C 20*(Polynomial.X+1)
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
noncomputable def queryExec (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool) (b:Bool) (p:Polynomial ℕ)
    (hA:EvalsToInTime (TM2.step A.program) (A.init (stream xs)) (some (A.halt [b])) (p.eval (stream xs).length)):
    EvalsToInTime (TM2.step (queryMachine n A).program) ((queryMachine n A).init (stream xs++s))
      (some ((queryMachine n A).halt ([b]++(stream xs++s)))) ((time p).eval (stream xs++s).length):=by
  have hp:=QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.polyExec n (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.allMask n) xs hx s
  rw [QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.fields_all] at hp
  have hd:=BitDelimiter.exec (raw xs)
  rw [MatrixListQuery.delimiter_raw xs (by intro h;subst xs;simp at hx)] at hd
  have hc:=Composition.executes BitDelimiter.machine A _ _ _ _ _ hd hA
  have hpc:=Composition.executes (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.prefixMachine n (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.allMask n))
    (Composition.machine BitDelimiter.machine A) _ _ _ _ _ hp hc
  have hr:=RetainedInput.executes
    (Composition.machine (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.prefixMachine n (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.allMask n))
      (Composition.machine BitDelimiter.machine A)) _ _ _ hpc
  refine {hr with steps_le_m:=hr.steps_le_m.trans ?_}
  have hpmono:=Composition.polynomial_eval_monotone p (show (stream xs).length≤(stream xs++s).length by simp)
  have hrlen:=raw_length_le xs
  simp only [QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.time,time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,List.length_cons,List.length_nil,List.length_append] at *
  omega
end QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery
