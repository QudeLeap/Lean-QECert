import QEC.Coding.BitTuring.UnaryMatrixListQuery

/-!
# Actual retained fixed-field computations

Fixed masks select fields on the input tape; real composition executes the supplied finite
program, appends its output delimiter, retains the complete original input or reverses the
selected fields. Actual output-stack growth, transfer and retention costs prove polynomial
bounds. Inputs, answers and correctness proofs do not enter the finite program's control.
These lower-level helpers are used by both complete original PSL group-operation programs.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.RetainedFieldComputation
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
/-- Combine two actual clean runs using real transfer costs and output-stack growth. -/
noncomputable def composeRuns (A B:Machine) (x y z:List Bool) (p r:Polynomial ℕ)
 (hA:EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt y)) (p.eval x.length))
 (hB:EvalsToInTime (TM2.step B.program) (B.init y) (some (B.halt z)) (r.eval y.length)):
 EvalsToInTime (TM2.step (Composition.machine A B).program) ((Composition.machine A B).init x)
 (some ((Composition.machine A B).halt z)) ((Composition.timePolynomial A p r).eval x.length):=by
 have hL:y.length≤(Composition.intermediateLengthPolynomial A p).eval x.length:=by
  simpa [Composition.intermediateLengthPolynomial,Nat.mul_comm] using Machine.output_length_le A x y _ hA
 have hr:=Composition.polynomial_eval_monotone r hL
 have hh:=Composition.executes A B x y z _ _ hA hB
 refine {hh with steps_le_m:=hh.steps_le_m.trans ?_}
 simp only [Composition.timePolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C]
 exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hr (Nat.mul_le_mul_left 2 hL)) 2) _
variable (n:ℕ) (keep:Fin (n+1)→Bool) (A:Machine)
/-- Execute the actual component and append a real field delimiter. -/
def marked:=Composition.machine A BitDelimiter.machine
/-- Polynomial counting the component and actual delimiter program. -/
noncomputable def markedTime (p:Polynomial ℕ):Polynomial ℕ:=Composition.timePolynomial A p (Polynomial.C 2*Polynomial.X+Polynomial.C 3)
/-- Physically select fixed fields, then execute the actual delimited component. -/
def projected:=Composition.machine (FieldProjection.machine n keep) (marked A)
/-- Polynomial counting field selection, component execution and delimiter transfer. -/
noncomputable def projectedTime (p:Polynomial ℕ):Polynomial ℕ:=Composition.timePolynomial (FieldProjection.machine n keep) FieldProjection.time (markedTime A p)
/-- Retain the entire original field stream while the selected actual component runs. -/
def machine:=RetainedInput.machine (projected n keep A)
/-- Whole retained fixed-field computation polynomial. -/
noncomputable def time (p:Polynomial ℕ):Polynomial ℕ:=RetainedInput.timePolynomial (projected n keep A) (projectedTime n keep A p)
/-- Actual selected-field execution returns the delimited result followed by the retained input. -/
noncomputable def exec (xs ys:List ℕ) (hx:xs.length=n+1) (hy:ys≠[]) (p:Polynomial ℕ)
 (hA:EvalsToInTime (TM2.step A.program) (A.init (raw (fields n keep 0 xs)))
  (some (A.halt (raw ys))) (p.eval (raw (fields n keep 0 xs)).length)):
 EvalsToInTime (TM2.step (machine n keep A).program) ((machine n keep A).init (stream xs))
  (some ((machine n keep A).halt (stream ys++stream xs))) ((time n keep A p).eval (stream xs).length):=by
 have hd:=BitDelimiter.exec (raw ys)
 rw [MatrixListQuery.delimiter_raw ys hy] at hd
 have ha:=RetainedFieldComputation.composeRuns A BitDelimiter.machine _ _ _ p (Polynomial.C 2*Polynomial.X+Polynomial.C 3) hA
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C] using hd)
 have hp:=FieldProjection.polyExec n keep xs hx
 have hc:=RetainedFieldComputation.composeRuns (FieldProjection.machine n keep) (marked A) _ _ _ FieldProjection.time (markedTime A p) hp ha
 exact RetainedInput.executes_polynomial (projected n keep A) (fun _:Unit=>stream xs)
  (fun _=>stream ys) (projectedTime n keep A p) (fun _=>hc) ()
end QEC.Coding.BitTuring.UnaryArithmetic.RetainedFieldComputation
namespace QEC.Coding.BitTuring.UnaryArithmetic.RetainedFieldComputation
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
/-- Actual component output receives a delimiter with complete scratch cleanup. -/
noncomputable def markedExec (A:Machine) (x:List Bool) (ys:List ℕ) (hy:ys≠[]) (p:Polynomial ℕ)
 (hA:EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt (raw ys))) (p.eval x.length)):
 EvalsToInTime (TM2.step (marked A).program) ((marked A).init x)
 (some ((marked A).halt (stream ys))) ((markedTime A p).eval x.length):=by
 have hd:=BitDelimiter.exec (raw ys)
 rw [MatrixListQuery.delimiter_raw ys hy] at hd
 exact RetainedFieldComputation.composeRuns A BitDelimiter.machine _ _ _ p (Polynomial.C 2*Polynomial.X+Polynomial.C 3) hA
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C] using hd)
/-- Execute the actual component with a delimiter while retaining its full original input. -/
def retainedMarked (A:Machine):=RetainedInput.machine (marked A)
/-- Polynomial counting actual component execution, marking and retention. -/
noncomputable def retainedMarkedTime (A:Machine) (p:Polynomial ℕ):=RetainedInput.timePolynomial (marked A) (markedTime A p)
/-- Actual marked component emits its result followed by the retained input. -/
noncomputable def retainedMarkedExec (A:Machine) (x:List Bool) (ys:List ℕ) (hy:ys≠[]) (p:Polynomial ℕ)
 (hA:EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt (raw ys))) (p.eval x.length)):
 EvalsToInTime (TM2.step (retainedMarked A).program) ((retainedMarked A).init x)
 (some ((retainedMarked A).halt (stream ys++x))) ((retainedMarkedTime A p).eval x.length):=
 RetainedInput.executes_polynomial (marked A) (fun _:Unit=>x) (fun _=>stream ys) (markedTime A p)
 (fun _=>markedExec A x ys hy p hA) ()
/-- Actual fixed-field projection followed by a real delimiter. -/
def projectedMarked (n:ℕ) (keep:Fin (n+1)→Bool):=Composition.machine (FieldProjection.machine n keep) BitDelimiter.machine
/-- Polynomial for the actual selected-field stream computation. -/
noncomputable def projectedMarkedTime (n:ℕ) (keep:Fin (n+1)→Bool):=Composition.timePolynomial (FieldProjection.machine n keep) FieldProjection.time (Polynomial.C 2*Polynomial.X+Polynomial.C 3)
/-- Actual field selection emits precisely the selected delimited stream. -/
noncomputable def projectedMarkedExec (n:ℕ) (keep:Fin (n+1)→Bool) (xs:List ℕ) (hx:xs.length=n+1)
 (hy:fields n keep 0 xs≠[]):
 EvalsToInTime (TM2.step (projectedMarked n keep).program) ((projectedMarked n keep).init (stream xs))
 (some ((projectedMarked n keep).halt (stream (fields n keep 0 xs)))) ((projectedMarkedTime n keep).eval (stream xs).length):=by
 have hd:=BitDelimiter.exec (raw (fields n keep 0 xs))
 rw [MatrixListQuery.delimiter_raw _ hy] at hd
 exact RetainedFieldComputation.composeRuns (FieldProjection.machine n keep) BitDelimiter.machine _ _ _ FieldProjection.time (Polynomial.C 2*Polynomial.X+Polynomial.C 3)
  (FieldProjection.polyExec n keep xs hx) (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C] using hd)
/-- Actual fixed-field projection followed by whole bit reversal. -/
def projectedReverse (n:ℕ) (keep:Fin (n+1)→Bool):=Composition.machine (FieldProjection.machine n keep) BitReverse.machine
/-- Polynomial for selecting and physically reversing the raw fields. -/
noncomputable def projectedReverseTime (n:ℕ) (keep:Fin (n+1)→Bool):=Composition.timePolynomial (FieldProjection.machine n keep) FieldProjection.time (Polynomial.X+1)
/-- Actual selection and reversal emit the exact reversed raw field word. -/
noncomputable def projectedReverseExec (n:ℕ) (keep:Fin (n+1)→Bool) (xs:List ℕ) (hx:xs.length=n+1):
 EvalsToInTime (TM2.step (projectedReverse n keep).program) ((projectedReverse n keep).init (stream xs))
 (some ((projectedReverse n keep).halt (raw (fields n keep 0 xs)).reverse)) ((projectedReverseTime n keep).eval (stream xs).length):=
 RetainedFieldComputation.composeRuns (FieldProjection.machine n keep) BitReverse.machine _ _ _ FieldProjection.time (Polynomial.X+1)
  (FieldProjection.polyExec n keep xs hx) (by simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using BitReverse.exec (raw (fields n keep 0 xs)))
end QEC.Coding.BitTuring.UnaryArithmetic.RetainedFieldComputation
