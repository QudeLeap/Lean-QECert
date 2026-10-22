import QEC.Coding.BitTuring.UnaryMultiplication
import Mathlib.Data.ZMod.Basic

/-!
# Actual unary remainder with a variable modulus

One fixed Boolean TM2, with four stacks, five labels and Option-Bool variables, takes the
faithful unary pair `(n,q)` with `q>0`. It parses both operands, cancels paired bits, restores
an exhausted modulus from the consumed prefix, and drains the remaining modulus when the
numerator runs out. The complete halt leaves unary `n%q`, empty auxiliary tapes and reset
variables. The modulus is on tape; neither the finite control nor the instruction tree depends
on it. Modulo occurs only in the proved specification, not in the program.

Counted execution takes `n+2*q+3+(n/q)*(2*q+2)` label steps, at most `5*(L+1)` for unary
encoded input length `L`. Standard Mathlib polynomial-time and canonical ZMod-residue output
certificates derive from this actual execution. This is unary input time; it is not a binary
natural-number bound or the complete explicit PK22 construction runtime. Boolean is the
encoding alphabet, and imposes no restriction on the quantum-code field.
-/
namespace QEC.Coding.BitTuring.UnaryArithmetic.Remainder
open Turing StateTransition
/-- The fixed finite Boolean instruction type used by the actual program. -/
abbrev Statement := TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool)
/-- Parse operands, cancel bits, restore the modulus and cleanly halt with the remainder. -/
def program : Fin 5 → Statement
  | 0 => .pop 0 (fun _ h => h)
      (.branch (fun v => v.getD false)
        (.push 1 (fun _ => true) (.goto fun _ => 0)) (.goto fun _ => 1))
  | 1 => .pop 0 (fun _ h => h)
      (.branch Option.isSome
        (.push 2 (fun _ => true) (.goto fun _ => 1)) (.goto fun _ => 2))
  | 2 => .pop 2 (fun _ h => h)
      (.branch Option.isSome
        (.pop 1 (fun _ h => h)
          (.branch Option.isSome
            (.push 3 (fun _ => true) (.goto fun _ => 2)) (.goto fun _ => 4)))
        (.goto fun _ => 3))
  | 3 => .pop 3 (fun _ h => h)
      (.branch Option.isSome
        (.push 2 (fun _ => true) (.goto fun _ => 3)) (.goto fun _ => 2))
  | _ => .pop 2 (fun _ h => h)
      (.branch Option.isSome (.goto fun _ => 4) (.load (fun _ => none) .halt))
/-- One fixed finite machine, independent of the input numerator and modulus. -/
def machine : Machine where
  K := Fin 4
  input := 0
  output := 3
  Λ := Fin 5
  main := 0
  σ := Option Bool
  initial := none
  program := program
/-- Concrete four-tape configuration for actual transition and phase proofs. -/
def cfg (l : Fin 5) (s n q r : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) := ⟨some l,v,![s,n,q,r]⟩
/-- Clean halt: only the output tape is populated, and finite variables are reset. -/
def halt (r : List Bool) : TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) :=
  ⟨none,none,![[],[],[],r]⟩
/-- One numerator bit is transferred from input to its working tape. -/
theorem parseN_cons (s n q r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 0 (true::s) n q r v)=some (cfg 0 s (true::n) q r (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k; fin_cases k <;> simp [Function.update]
/-- The separator changes the actual parser label without altering the working tapes. -/
theorem parseN_sep (s n q r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 0 (false::s) n q r v)=some (cfg 1 s n q r (some false)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k; fin_cases k <;> simp [Function.update]
/-- One modulus bit is transferred from input to its working tape. -/
theorem parseQ_cons (s n q r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 1 (true::s) n q r v)=some (cfg 1 s n (true::q) r (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k; fin_cases k <;> simp [Function.update]
/-- The empty input enters the actual cancellation loop. -/
theorem parseQ_nil (n q r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 1 [] n q r v)=some (cfg 2 [] n q r none) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- One bit is consumed from both operands and saved in the remainder buffer. -/
theorem scan_cons (n q r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 2 [] (true::n) (true::q) r v)=
      some (cfg 2 [] n q (true::r) (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k; fin_cases k <;> simp [Function.update]
/-- An exhausted modulus switches to actual restoration. -/
theorem scan_q_nil (n r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 2 [] n [] r v)=some (cfg 3 [] n [] r none) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- An exhausted numerator switches to actual cleanup after consuming one modulus bit. -/
theorem scan_n_nil (q r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 2 [] [] (true::q) r v)=some (cfg 4 [] [] q r none) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k; fin_cases k <;> simp [Function.update]
/-- One saved modulus bit is restored to the modulus tape. -/
theorem restore_cons (n q r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 3 [] n q (true::r) v)=some (cfg 3 [] n (true::q) r (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k; fin_cases k <;> simp [Function.update]
/-- Emptying the buffer returns to the cancellation loop with reset variables. -/
theorem restore_nil (n q : List Bool) (v : Option Bool) :
    TM2.step program (cfg 3 [] n q [] v)=some (cfg 2 [] n q [] none) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Cleanup discards one remaining modulus bit. -/
theorem drain_cons (q r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 4 [] [] (true::q) r v)=some (cfg 4 [] [] q r (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k; fin_cases k <;> simp [Function.update]
/-- Empty auxiliary tapes cause the actual reset and halt. -/
theorem drain_nil (r : List Bool) (v : Option Bool) :
    TM2.step program (cfg 4 [] [] [] r v)=some (halt r) := by
  simp [TM2.step,program,cfg,halt,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Complete numerator parsing, including the separator, in m+1 actual steps. -/
theorem parseN_run (m : ℕ) (s n q r : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[m+1]
      (some (cfg 0 (unary m++false::s) n q r v))=
      some (cfg 1 s (unary m++n) q r (some false)) := by
  induction m generalizing n v with
  | zero => simp [parseN_sep]
  | succ m ih =>
      rw [unary_succ,List.cons_append,Function.iterate_succ_apply]
      simp only [Option.bind_some,parseN_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true::n) (some true)
/-- Complete modulus parsing, including the empty-input transition, in m+1 steps. -/
theorem parseQ_run (m : ℕ) (n q r : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[m+1]
      (some (cfg 1 (unary m) n q r v))=
      some (cfg 2 [] n (unary m++q) r none) := by
  induction m generalizing q v with
  | zero => simp [parseQ_nil]
  | succ m ih =>
      rw [unary_succ,Function.iterate_succ_apply]
      simp only [Option.bind_some,parseQ_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true::q) (some true)
/-- Counted cancellation of any common unary prefix preserves the exact remaining tapes. -/
theorem scan_run (m n q r : ℕ) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[m]
      (some (cfg 2 [] (unary (n+m)) (unary (q+m)) (unary r) v))=
      some (cfg 2 [] (unary n) (unary q) (unary (r+m)) (if m=0 then v else some true)) := by
  induction m generalizing n q r v with
  | zero => simp
  | succ m ih =>
      simp only [Nat.add_succ,Nat.add_zero,unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,scan_cons]
      have h := ih n q (r+1) (some true)
      rw [show r+1+m=r+m+1 by omega] at h
      simp only [unary_succ,ite_self] at h
      simpa only [ite_self,Nat.succ_ne_zero,if_false] using h
/-- Restore all buffered modulus bits and reset the variables in m+1 steps. -/
theorem restore_run (m : ℕ) (n q : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[m+1]
      (some (cfg 3 [] n q (unary m) v))=some (cfg 2 [] n (unary m++q) [] none) := by
  induction m generalizing q v with
  | zero => simp [restore_nil]
  | succ m ih =>
      rw [unary_succ,Function.iterate_succ_apply]
      simp only [Option.bind_some,restore_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true::q) (some true)
/-- Discard the remaining modulus tape and produce a clean halt in m+1 steps. -/
theorem drain_run (m : ℕ) (r : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[m+1]
      (some (cfg 4 [] [] (unary m) r v))=some (halt r) := by
  induction m generalizing v with
  | zero => simp [drain_nil]
  | succ m ih =>
      rw [unary_succ,Function.iterate_succ_apply]
      simp only [Option.bind_some,drain_cons]
      exact ih (some true)

/-- One complete cancellation/restoration cycle removes exactly q numerator bits. -/
theorem cycle_run (q n : ℕ) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[2*q+2]
      (some (cfg 2 [] (unary (n+q)) (unary q) [] v))=
      some (cfg 2 [] (unary n) (unary q) [] none) := by
  have hs := scan_run q n 0 0 v
  simp only [Nat.zero_add,show unary 0=[] from rfl] at hs
  rw [show 2*q+2=(q+2)+q by omega,Function.iterate_add_apply,hs]
  rw [show q+2=(q+1)+1 by omega,Function.iterate_add_apply,Function.iterate_one]
  simp only [Option.bind_some,scan_q_nil]
  rw [restore_run]
  simp only [List.append_nil]

/-- Iterated actual cycles remove k*q bits while restoring the same tape modulus. -/
theorem cycles_run (q k r : ℕ) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[k*(2*q+2)]
      (some (cfg 2 [] (unary (r+k*q)) (unary q) [] v))=
      some (cfg 2 [] (unary r) (unary q) [] (if k=0 then v else none)) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul,Function.iterate_add_apply,
        show r+(k+1)*q=(r+k*q)+q by ring,cycle_run,ih]
      simp

/-- For r<q, the last partial cancellation drains the modulus and outputs exactly r. -/
theorem final_run (q r : ℕ) (hr : r<q) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[q+1]
      (some (cfg 2 [] (unary r) (unary q) [] v))=some (halt (unary r)) := by
  let t := q-r-1
  have hq : q=(t+1)+r := by dsimp [t]; omega
  have hs := scan_run r 0 (t+1) 0 v
  simp only [Nat.zero_add,show unary 0=[] from rfl] at hs
  rw [show q+1=(t+2)+r by omega,Function.iterate_add_apply,hq,hs]
  rw [show t+2=(t+1)+1 by omega,Function.iterate_add_apply,Function.iterate_one,unary_succ]
  simp only [Option.bind_some,scan_n_nil]
  exact drain_run t (unary r) none

/-- The natural division algorithm identifies the true loop result as the remainder. -/
theorem run_body (n q : ℕ) (hq : 0<q) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n/q*(2*q+2)+(q+1)]
      (some (cfg 2 [] (unary n) (unary q) [] v))=some (halt (unary (n%q))) := by
  rw [show n/q*(2*q+2)+(q+1)=(q+1)+n/q*(2*q+2) by omega,Function.iterate_add_apply]
  have hn : n=n%q+(n/q)*q := by simpa only [Nat.mul_comm] using (Nat.mod_add_div n q).symm
  have hc := cycles_run q (n/q) (n%q) v
  rw [←hn] at hc
  rw [hc]
  exact final_run q (n%q) (Nat.mod_lt n hq) _

/-- Complete label-step count, including input parsing, restoration and cleanup. -/
def steps (n q : ℕ) : ℕ := n+2*q+3+(n/q)*(2*q+2)

/-- Both operands are actually parsed from the faithful pair encoding. -/
theorem parse_run (n q : ℕ) :
    (fun c => c.bind (TM2.step program))^[n+q+2]
      (some (cfg 0 (pairInput n q) [] [] [] none))=
      some (cfg 2 [] (unary n) (unary q) [] none) := by
  rw [show n+q+2=(q+1)+(n+1) by omega,Function.iterate_add_apply]
  simp only [pairInput]
  rw [parseN_run,parseQ_run]
  simp only [List.append_nil]

/-- The full instruction execution reaches the exact clean remainder configuration. -/
theorem run (n q : ℕ) (hq : 0<q) :
    (fun c => c.bind (TM2.step program))^[steps n q]
      (some (cfg 0 (pairInput n q) [] [] [] none))=
      some (halt (unary (n%q))) := by
  rw [show steps n q=(n/q*(2*q+2)+(q+1))+(n+q+2) by unfold steps; omega,
    Function.iterate_add_apply,parse_run]
  exact run_body n q hq none

/-- The standard machine initial state equals the concrete parser configuration. -/
theorem init_eq (n q : ℕ) : machine.init (pairInput n q)=cfg 0 (pairInput n q) [] [] [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k; fin_cases k <;> simp [Function.update]

/-- The standard machine halt equals the concrete clean output configuration. -/
theorem halt_eq (r : List Bool) : machine.halt r=halt r := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k; fin_cases k <;> simp [Function.update]

/-- Counted execution certificate derived from the actual whole-run theorem. -/
def exec (n q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (pairInput n q))
      (some (machine.halt (unary (n%q)))) (steps n q) := by
  refine ⟨⟨steps n q,?_⟩,le_refl _⟩
  rw [init_eq,halt_eq]
  exact run n q hq

/-- Complete execution is linear in the actual unary encoded-input length. -/
theorem steps_le (n q : ℕ) : steps n q ≤ 5*((pairInput n q).length+1) := by
  rw [pairInput_length]
  have hdiv : n/q≤n := Nat.div_le_self n q
  have hmul : n/q*q≤n := Nat.div_mul_le_self n q
  have h2 : n/q*(2*q+2)≤2*n+2*n := by
    calc
      n/q*(2*q+2)=2*(n/q*q)+2*(n/q) := by ring
      _≤2*n+2*n := Nat.add_le_add (Nat.mul_le_mul_left 2 hmul) (Nat.mul_le_mul_left 2 hdiv)
  unfold steps
  omega

/-- The linear polynomial used by the standard execution certificate. -/
noncomputable def time : Polynomial ℕ := Polynomial.C 5*(Polynomial.X+1)
/-- The actual execution certificate bounded by the linear input-length polynomial. -/
noncomputable def polyExec (n q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (pairInput n q))
      (some (machine.halt (unary (n%q)))) (time.eval (pairInput n q).length) := by
  have h := exec n q hq
  refine {h with steps_le_m := h.steps_le_m.trans ?_}
  simpa [time] using steps_le n q

/-- Standard Mathlib output certificate for the actual remainder machine. -/
noncomputable def outputsInTime (n q : ℕ) (hq : 0<q) :
    TM2OutputsInTime machine.toFinTM2 (pairInput n q) (some (unary (n%q)))
      (time.eval (pairInput n q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec n q hq)

/-- The same actual output is the canonical value of the genuine ZMod residue. -/
noncomputable def outputsZModValInTime (n q : ℕ) (hq : 0<q) :
    TM2OutputsInTime machine.toFinTM2 (pairInput n q) (some (unary ((n:ZMod q).val)))
      (time.eval (pairInput n q).length) := by
  let : NeZero q := ⟨hq.ne'⟩
  simpa only [ZMod.val_natCast] using outputsInTime n q hq

/-- Faithful unary input for a natural numerator and a positive dynamic modulus. -/
def input (x : ℕ×ℕ+) : List Bool := pairInput x.1 x.2.val

/-- The actual pair encoding distinguishes every positive-modulus input. -/
theorem input_injective : Function.Injective input := by
  intro x y h
  have hh := @pairInput_injective (x.1,x.2.val) (y.1,y.2.val) h
  have ha : x.1=y.1 := congrArg (fun z:ℕ×ℕ => z.1) hh
  have hq : x.2.val=y.2.val := congrArg (fun z:ℕ×ℕ => z.2) hh
  exact Prod.ext ha (Subtype.ext hq)

/-- Standard polynomial-time computation of remainder for every positive modulus. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime input unary (fun x : ℕ×ℕ+ => x.1%x.2.val) where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun x => by
    change TM2OutputsInTime machine.toFinTM2
      (List.map id (input x)) (some (List.map id (unary (x.1%x.2.val))))
      (time.eval (input x).length)
    have h := outputsInTime x.1 x.2.val x.2.pos
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input] using h

end QEC.Coding.BitTuring.UnaryArithmetic.Remainder
