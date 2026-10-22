import QEC.Coding.BitTuring.UnaryFieldProjection
import QEC.Coding.BitTuring.UnaryInverseInput
import QEC.Coding.BitTuring.RetainedInput

/-!
# Actual retained query of an original modulus field

A fixed finite field selector reads only the original last q field. The wrapper executes the
actual supplied q-only body program, actually writes its output delimiter and retains every
prior field. Its structural selection/arity and independently proved actual body run imply
complete clean execution with all projection, transfer, delimiter and retention costs.
Source consumers instantiate the helper with actual signed/root/inverse programs; no
semantic answer, execution or cost field is stored inside the finite machine.
-/

namespace QEC.Coding.BitTuring.ModulusQuery
open Turing StateTransition UnaryArithmetic FieldProjection
/-- The finite selector reads only the original last modulus field. -/
def mask (n:ℕ) (k:Fin (n+1)) : Bool := k.val==n
/-- Real projection, q-only body run, delimiter and input retention. -/
def machine (n:ℕ) (A:Machine) := RetainedInput.machine
  (Composition.machine (FieldProjection.machine n (mask n)) (Composition.machine A UnaryDelimiter.machine))
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def time (p:Polynomial ℕ) := p+Polynomial.C 20*(Polynomial.X+1)
/-- Generic structural wrapper is instantiated below with proved actual arithmetic programs. -/
noncomputable def exec (n:ℕ) (A:Machine) (p:Polynomial ℕ) (xs:List ℕ)
    (hx:xs.length=n+1) (q r:ℕ) (hr:r<q)
    (hf:fields n (mask n) 0 xs=[q])
    (hA:EvalsToInTime (TM2.step A.program) (A.init (unary q))
      (some (A.halt (unary r))) (p.eval q)) :
    EvalsToInTime (TM2.step (machine n A).program) ((machine n A).init (stream xs))
      (some ((machine n A).halt (stream (r::xs)))) ((time p).eval (stream xs).length) := by
  have hp:=FieldProjection.polyExec n (mask n) xs hx
  rw [hf] at hp
  have he:raw [q]=unary q := by
    simpa only [List.nil_append,stream,List.append_nil] using raw_append_last [] q
  rw [he] at hp
  have hb:=Composition.executes A UnaryDelimiter.machine _ _ _ _ _ hA (UnaryDelimiter.exec r)
  have hbody:=Composition.executes (FieldProjection.machine n (mask n))
    (Composition.machine A UnaryDelimiter.machine) _ _ _ _ _ hp hb
  have h:=RetainedInput.executes
    (Composition.machine (FieldProjection.machine n (mask n)) (Composition.machine A UnaryDelimiter.machine))
    (stream xs) (unary r++[false]) _ hbody
  rw [show (unary r++[false])++stream xs=stream (r::xs) by simp [stream,List.append_assoc]] at h
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hl:=fields_stream_length_le n (mask n) 0 xs
  rw [hf] at hl
  have hs:(stream [q]).length=q+1 := by simp [stream,unary_length]
  rw [hs] at hl
  have hpol:=Composition.polynomial_eval_monotone p (show q≤(stream xs).length by omega)
  change p.eval q≤p.eval (stream xs).length at hpol
  simp only [time,FieldProjection.time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,List.length_append,List.length_singleton,unary_length]
  omega
end QEC.Coding.BitTuring.ModulusQuery
