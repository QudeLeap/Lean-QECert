import QEC.Coding.BitTuring.ModulusQuery
import QEC.Coding.BitTuring.BitDelimiters
import QEC.Coding.BitTuring.RetainedInput
import Mathlib.Tactic.Linarith

/-!
# Actual retained four-entry matrix-list query

Real fixed last-q projection executes a proved actual q-only body, adds a genuine payload
separator and retains all preceding fields and q. Structural selection, canonical four-entry
bounds and actual transfer costs imply the whole query budget; no semantic answer/cost field
enters the finite instructions. Empty-list collection uses two actual reversal loops.
Stream/selection specifications and budgets are mathematical invariants, never callbacks.
Source consumers instantiate the query with the actual original normalized SL program.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.MatrixListQuery
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection

/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem stream_append (xs ys:List ℕ) : stream (xs++ys)=stream xs++stream ys := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.cons_append,stream,ih,List.append_assoc,List.cons_append]
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem stream_length_bound (q:ℕ) (xs:List ℕ) (h:∀x∈xs,x<q) :
    (stream xs).length≤xs.length*(q+1) := by
  induction xs with
  | nil=>simp [stream]
  | cons x xs ih=>
    have hx:=h x (by simp)
    have ht:=ih (fun z hz=>h z (by simp [hz]))
    simp only [stream,List.length_append,List.length_cons,unary_length]
    nlinarith
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem delimiter_raw (xs:List ℕ) (h:xs≠[]) : raw xs++[false]=stream xs := by
  induction xs with
  | nil=>contradiction
  | cons x xs ih=>
    cases xs with
    | nil=>simp [raw,stream]
    | cons y ys=>
      have hn:stream (y::ys)≠[] := by
        intro he
        have hl:=congrArg List.length he
        simp only [stream_length,List.length_nil,List.length_cons] at hl
        omega
      change (unary x++false::stream (y::ys)).dropLast++[false]=_
      rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),List.dropLast_cons_of_ne_nil hn]
      simpa only [List.append_assoc,List.cons_append,stream,raw] using
        congrArg (fun w=>unary x++false::w) (ih (by simp))

/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def prefixMask (n:ℕ) (k:Fin (n+1)):Bool := k.val<n
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem selectLast (n i:ℕ) (xs:List ℕ) (q:ℕ) (hi:i+xs.length=n) :
    fields n (ModulusQuery.mask n) i (xs++[q])=[q] := by
  induction xs generalizing i with
  | nil=>
    have he:i=n :=by simpa using hi
    subst i
    simp [fields,maskAt,ModulusQuery.mask,Nat.mod_eq_of_lt (show n<n+1 by omega)]
  | cons x xs ih=>
    have hl:i<n :=by simp only [List.length_cons] at hi;omega
    have ht:i+1+xs.length=n :=by simp only [List.length_cons] at hi;omega
    have he:i≠n := by omega
    simp only [List.cons_append,fields,maskAt,ModulusQuery.mask,
      Nat.mod_eq_of_lt (show i<n+1 by omega),beq_eq_false_iff_ne.mpr he,Bool.false_eq_true,↓reduceIte]
    exact ih (i+1) ht
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 theorem selectPrefix (n i:ℕ) (xs:List ℕ) (q:ℕ) (hi:i+xs.length=n) :
    fields n (prefixMask n) i (xs++[q])=xs := by
  induction xs generalizing i with
  | nil=>
    have he:i=n :=by simpa using hi
    subst i
    simp [fields,maskAt,prefixMask,Nat.mod_eq_of_lt (show n<n+1 by omega)]
  | cons x xs ih=>
    have hl:i<n :=by simp only [List.length_cons] at hi;omega
    have ht:i+1+xs.length=n :=by simp only [List.length_cons] at hi;omega
    simp only [List.cons_append,fields,maskAt,prefixMask,
      Nat.mod_eq_of_lt (show i<n+1 by omega),hl,decide_true,↓reduceIte]
    congr 1
    exact ih (i+1) ht

/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def queryMachine (n:ℕ) (A:Machine) := RetainedInput.machine
   (Composition.machine (FieldProjection.machine n (ModulusQuery.mask n))
     (Composition.machine A BitDelimiter.machine))
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 noncomputable def queryExec (n:ℕ) (A:Machine) (p:Polynomial ℕ) (xs ys:List ℕ)
    (q:ℕ) (hx:xs.length=n) (hy:ys.length=4) (hb:∀y∈ys,y<q)
    (hA:EvalsToInTime (TM2.step A.program) (A.init (unary q))
      (some (A.halt (raw ys))) (p.eval q)) :
    EvalsToInTime (TM2.step (queryMachine n A).program)
      ((queryMachine n A).init (stream (xs++[q])))
      (some ((queryMachine n A).halt (stream (ys++xs++[q]))))
      (p.eval q+50*((stream (xs++[q])).length+1)) := by
  have hp:=FieldProjection.polyExec n (ModulusQuery.mask n) (xs++[q]) (by simp [hx])
  rw [selectLast n 0 xs q (by simpa using hx)] at hp
  have he:raw [q]=unary q := by simpa [stream] using raw_append_last [] q
  rw [he] at hp
  have hn:ys≠[] :=by intro h; simp [h] at hy
  have hd:=BitDelimiter.exec (raw ys)
  rw [delimiter_raw ys hn] at hd
  have hab:=Composition.executes A BitDelimiter.machine _ _ _ _ _ hA hd
  have hc:=Composition.executes (FieldProjection.machine n (ModulusQuery.mask n))
    (Composition.machine A BitDelimiter.machine) _ _ _ _ _ hp hab
  have hr:=RetainedInput.executes
    (Composition.machine (FieldProjection.machine n (ModulusQuery.mask n))
      (Composition.machine A BitDelimiter.machine)) _ _ _ hc
  rw [←stream_append,←List.append_assoc] at hr
  refine {hr with steps_le_m:=hr.steps_le_m.trans ?_}
  have hL:q+1≤(stream (xs++[q])).length :=by
    rw [stream_append]
    simp [stream,unary_length]
  have hY:(stream ys).length≤4*(q+1) :=by simpa [hy] using stream_length_bound q ys hb
  have hR:=raw_length_le ys
  simp only [FieldProjection.time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,unary_length]
  omega

/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def identityMachine:=Composition.machine BitReverse.machine BitReverse.machine
/-- Actual finite instruction construction or proved invariant, whole execution, budget or source certificate. -/
 def identityExec (w:List Bool) : EvalsToInTime (TM2.step identityMachine.program)
    (identityMachine.init w) (some (identityMachine.halt w)) (4*w.length+4) :=by
  have h:=Composition.executes BitReverse.machine BitReverse.machine _ _ _ _ _
    (BitReverse.exec w) (BitReverse.exec w.reverse)
  rw [List.reverse_reverse,List.length_reverse] at h
  exact {h with steps_le_m:=h.steps_le_m.trans (by omega)}
end QEC.Coding.BitTuring.UnaryArithmetic.MatrixListQuery
