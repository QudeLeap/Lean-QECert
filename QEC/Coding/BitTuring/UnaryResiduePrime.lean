import QEC.Coding.BitTuring.UnaryPrimality

/-!
# Actual least eligible-prime scanning

For each fixed positive modulus, this finite Boolean program first writes
`max B m + 1` from the unary bound B, then repeatedly invokes the real primality
machine, computes the residue with a finite counter, and stops at the first
eligible prime. Both the lower-bound writer and residue updater have proved
complete scan/restore executions, with all non-output tapes drained and variables
reset. The initial writer uses a saturated `Fin (m+1)` counter and a literal push
instruction tree indexed by a finite label; natural recursion builds the fixed
program and never becomes unbounded runtime state.

The actual retained-input primality/residue body has a standard computation
certificate on candidates at least two. Actual loop executions follow from a
strictly decreasing endpoint-minus-candidate rank, and composition constructs
complete execution from the original bound. The derived quintic polynomial is
in the selected output length. No prime-gap estimate or polynomial bound in B
is assumed. Endpoint eligibility and minimality are mathematical inputs to the
generic execution proof; the LPS source bridge derives both for its original
Dirichlet/Nat.find selector.

This proves prime-selection execution, not the full PSL/finite-field/sparse CSS
emission runtime or the unconditional spectral estimate needed by the PK22 main
theorem. Boolean is the machine alphabet, with no quantum-code field restriction.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.LowerBound
open Turing StateTransition

abbrev Var (m : ℕ) := Fin (m+1) × Option Bool
abbrev Label (m : ℕ) := Bool ⊕ Fin (m+1)
abbrev Statement (m : ℕ) := TM2.Stmt (fun _ : Fin 3 => Bool) (Label m) (Var m)
def reset (m : ℕ) : Var m := (⟨0,by omega⟩,none)
def next (m : ℕ) (r : Fin (m+1)) : Fin (m+1) := ⟨min m (r.val+1),by have := Nat.min_le_left m (r.val+1);omega⟩
def after (m : ℕ) (r : Fin (m+1)) (n : ℕ) : Fin (m+1) := ⟨min m (r.val+n),by have := Nat.min_le_left m (r.val+n);omega⟩

/-- A fixed literal-push instruction tree; its length is chosen when constructing a finite label. -/
def pushN (m : ℕ) : ℕ → Statement m
  | 0 => .load (fun _ => reset m) .halt
  | n+1 => .push 2 (fun _ => true) (pushN m n)

/-- Scan the unary bound, restore it, then dispatch to its finite saturated-counter prefix. -/
def program (m : ℕ) : Label m → Statement m
  | .inl true => .pop 0 (fun v h => (v.1,h))
      (.branch (fun v => v.2.isSome)
        (.push 1 (fun _ => true) (.load (fun v => (next m v.1,none)) (.goto fun _ => .inl true)))
        (.goto fun _ => .inl false))
  | .inl false => .pop 1 (fun v h => (v.1,h))
      (.branch (fun v => v.2.isSome)
        (.push 2 (fun _ => true) (.load (fun v => (v.1,none)) (.goto fun _ => .inl false)))
        (.goto fun v => .inr v.1))
  | .inr r => pushN m (m-r.val+1)

def machine (m : ℕ) : Machine where
  K := Fin 3
  input := 0
  output := 2
  Λ := Label m
  main := .inl true
  σ := Var m
  initial := reset m
  program := program m

def cfg (m : ℕ) (l : Label m) (s b d : List Bool) (r : Fin (m+1)) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Label m) (Var m) := ⟨some l,(r,none),![s,b,d]⟩
def halt (m : ℕ) (d : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Label m) (Var m) := ⟨none,reset m,![[],[],d]⟩

theorem after_zero (m : ℕ) (r : Fin (m+1)) : after m r 0=r := by
  apply Fin.ext
  have := r.isLt
  simp only [after,Fin.val_mk,Nat.add_zero]
  omega

theorem after_next (m : ℕ) (r : Fin (m+1)) (n : ℕ) : after m (next m r) n=after m r (n+1) := by
  apply Fin.ext
  simp only [after,next,Fin.val_mk]
  omega

theorem scan_cons (m : ℕ) (r : Fin (m+1)) (s b d : List Bool) :
    TM2.step (program m) (cfg m (.inl true) (true::s) b d r) =
      some (cfg m (.inl true) s (true::b) d (next m r)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

theorem scan_nil (m : ℕ) (r : Fin (m+1)) (b d : List Bool) :
    TM2.step (program m) (cfg m (.inl true) [] b d r) = some (cfg m (.inl false) [] b d r) := by
  simp [TM2.step,program,cfg,TM2.stepAux]

theorem restore_cons (m : ℕ) (r : Fin (m+1)) (s b d : List Bool) :
    TM2.step (program m) (cfg m (.inl false) s (true::b) d r) =
      some (cfg m (.inl false) s b (true::d) r) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

theorem restore_nil (m : ℕ) (r : Fin (m+1)) (d : List Bool) :
    TM2.step (program m) (cfg m (.inl false) [] [] d r) = some (cfg m (.inr r) [] [] d r) := by
  simp [TM2.step,program,cfg,TM2.stepAux]

theorem pushAux (m n : ℕ) (v : Var m) (S : Fin 3 → List Bool) :
    TM2.stepAux (pushN m n) v S = ⟨none,reset m,Function.update S 2 (unary n++S 2)⟩ := by
  induction n generalizing S with
  | zero => simp [pushN,TM2.stepAux,unary]
  | succ n ih =>
      simp only [pushN,TM2.stepAux]
      rw [ih]
      simp [unary_append_cons,unary_succ]

theorem emit (m : ℕ) (r : Fin (m+1)) (d : List Bool) :
    TM2.step (program m) (cfg m (.inr r) [] [] d r) = some (halt m (unary (m-r.val+1)++d)) := by
  simp [TM2.step,program,cfg,pushAux,halt,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

theorem scan_run (m : ℕ) (r : Fin (m+1)) (n : ℕ) (b d : List Bool) :
    (fun c => c.bind (TM2.step (program m)))^[n+1] (some (cfg m (.inl true) (unary n) b d r)) =
      some (cfg m (.inl false) [] (unary n++b) d (after m r n)) := by
  induction n generalizing r b with
  | zero => simpa [unary,after_zero] using scan_nil m r b d
  | succ n ih =>
      rw [unary_succ,Function.iterate_succ_apply]
      simp only [Option.bind_some,scan_cons]
      rw [ih,after_next]
      simp [unary_append_cons,unary_succ]

theorem restore_run (m : ℕ) (r : Fin (m+1)) (n : ℕ) (d : List Bool) :
    (fun c => c.bind (TM2.step (program m)))^[n+1] (some (cfg m (.inl false) [] (unary n) d r)) =
      some (cfg m (.inr r) [] [] (unary n++d) r) := by
  induction n generalizing d with
  | zero => simpa [unary] using restore_nil m r d
  | succ n ih =>
      rw [unary_succ,Function.iterate_succ_apply]
      simp only [Option.bind_some,restore_cons]
      rw [ih]
      simp [unary_append_cons,unary_succ]

theorem run (m B : ℕ) :
    (fun c => c.bind (TM2.step (program m)))^[2*B+3]
      (some (cfg m (.inl true) (unary B) [] [] ⟨0,by omega⟩)) = some (halt m (unary (max B m+1))) := by
  rw [show 2*B+3=1+((B+1)+(B+1)) by omega,Function.iterate_add_apply,Function.iterate_add_apply,scan_run]
  simp only [List.append_nil]
  rw [restore_run]
  simp only [List.append_nil,Function.iterate_one,Option.bind_some,emit]
  have he : m-(after m ⟨0,by omega⟩ B).val+1+B=max B m+1 := by simp only [after,Fin.val_mk,Nat.zero_add];omega
  rw [← unary_add,he]

theorem init_eq (m B : ℕ) : (machine m).init (unary B)=cfg m (.inl true) (unary B) [] [] ⟨0,by omega⟩ := by
  simp [Machine.init,machine,cfg,reset,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

theorem halt_eq (m : ℕ) (d : List Bool) : (machine m).halt d=halt m d := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Complete actual lower-bound execution, with reset and all other tapes empty. -/
def executes (m B : ℕ) :
    EvalsToInTime (TM2.step (machine m).program) ((machine m).init (unary B))
      (some ((machine m).halt (unary (max B m+1)))) (2*B+3) := by
  refine ⟨⟨2*B+3,?_⟩,le_refl _⟩
  exact (init_eq m B).symm ▸ (halt_eq m (unary (max B m+1))).symm ▸ run m B

end QEC.Coding.BitTuring.UnaryArithmetic.LowerBound

namespace QEC.Coding.BitTuring.UnaryArithmetic.ResiduePrime
open Turing StateTransition

abbrev Var (m : ℕ) := Fin m × Bool × Option Bool
abbrev Statement (m : ℕ) := TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 3) (Var m)

def reset (m : ℕ) (hm : 0 < m) : Var m := (⟨0,hm⟩,false,none)
def next (m : ℕ) (hm : 0 < m) (r : Fin m) : Fin m := ⟨(r.val+1)%m,Nat.mod_lt _ hm⟩
def after (m : ℕ) (hm : 0 < m) (r : Fin m) (n : ℕ) : Fin m := ⟨(r.val+n)%m,Nat.mod_lt _ hm⟩

/-- Read the prime flag, scan with a bounded residue counter, restore and finish or increment. -/
def program (m : ℕ) (hm : 0 < m) : Fin 3 → Statement m
  | 0 => .pop 0 (fun v h => (v.1,h.getD false,none)) (.goto fun _ => 1)
  | 1 => .pop 0 (fun v h => (v.1,v.2.1,h))
      (.branch (fun v => v.2.2.isSome)
        (.push 1 (fun _ => true) (.load (fun v => (next m hm v.1,v.2.1,none)) (.goto fun _ => 1)))
        (.load (fun v => (v.1,v.2.1,none)) (.goto fun _ => 2)))
  | _ => .pop 1 (fun v h => (v.1,v.2.1,h))
      (.branch (fun v => v.2.2.isSome)
        (.push 2 (fun _ => true) (.load (fun v => (v.1,v.2.1,none)) (.goto fun _ => 2)))
        (.branch (fun v => v.2.1 && decide (v.1.val=1))
          (.push 2 (fun _ => true) (.load (fun _ => reset m hm) .halt))
          (.push 2 (fun _ => true) (.push 2 (fun _ => false) (.load (fun _ => reset m hm) .halt)))))

def machine (m : ℕ) (hm : 0 < m) : Machine where
  K := Fin 3
  input := 0
  output := 2
  Λ := Fin 3
  main := 0
  σ := Var m
  initial := reset m hm
  program := program m hm

def cfg (m : ℕ) (l : Fin 3) (s b d : List Bool) (r : Fin m) (p : Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Var m) := ⟨some l,(r,p,none),![s,b,d]⟩

def halt (m : ℕ) (hm : 0 < m) (d : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Var m) := ⟨none,reset m hm,![[],[],d]⟩

theorem after_zero (m : ℕ) (hm : 0 < m) (r : Fin m) : after m hm r 0=r := by
  apply Fin.ext
  simp [after,Nat.mod_eq_of_lt r.isLt]

theorem after_next (m : ℕ) (hm : 0 < m) (r : Fin m) (n : ℕ) :
    after m hm (next m hm r) n=after m hm r (n+1) := by
  apply Fin.ext
  simp only [after,next,Fin.val_mk]
  simp only [Nat.mod_add_mod]
  congr 1
  omega

theorem read_flag (m : ℕ) (hm : 0 < m) (p : Bool) (s : List Bool) :
    TM2.step (program m hm) (cfg m 0 (p::s) [] [] ⟨0,hm⟩ false) =
      some (cfg m 1 s [] [] ⟨0,hm⟩ p) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

theorem scan_cons (m : ℕ) (hm : 0 < m) (r : Fin m) (p : Bool) (s b d : List Bool) :
    TM2.step (program m hm) (cfg m 1 (true::s) b d r p) =
      some (cfg m 1 s (true::b) d (next m hm r) p) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

theorem scan_nil (m : ℕ) (hm : 0 < m) (r : Fin m) (p : Bool) (b d : List Bool) :
    TM2.step (program m hm) (cfg m 1 [] b d r p) = some (cfg m 2 [] b d r p) := by
  simp [TM2.step,program,cfg,TM2.stepAux]

theorem restore_cons (m : ℕ) (hm : 0 < m) (r : Fin m) (p : Bool) (s b d : List Bool) :
    TM2.step (program m hm) (cfg m 2 s (true::b) d r p) =
      some (cfg m 2 s b (true::d) r p) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

theorem restore_nil (m : ℕ) (hm : 0 < m) (r : Fin m) (p : Bool) (d : List Bool) :
    TM2.step (program m hm) (cfg m 2 [] [] d r p) =
      some (halt m hm (if p && decide (r.val=1) then true::d else false::true::d)) := by
  cases p <;> by_cases hr : r.val=1
  all_goals simp [TM2.step,program,cfg,halt,reset,TM2.stepAux,TM2.Cfg.mk.injEq,hr]
  all_goals funext k; fin_cases k <;> simp [Function.update]

theorem scan_run (m : ℕ) (hm : 0 < m) (r : Fin m) (p : Bool) (n : ℕ) (b d : List Bool) :
    (fun c => c.bind (TM2.step (program m hm)))^[n] (some (cfg m 1 (unary n) b d r p)) =
      some (cfg m 1 [] (unary n++b) d (after m hm r n) p) := by
  induction n generalizing r b with
  | zero => simp [unary,after_zero]
  | succ n ih =>
      rw [unary_succ,Function.iterate_succ_apply]
      simp only [Option.bind_some,scan_cons]
      rw [ih,after_next]
      simp [unary_append_cons,unary_succ]

theorem restore_run (m : ℕ) (hm : 0 < m) (r : Fin m) (p : Bool) (n : ℕ) (d : List Bool) :
    (fun c => c.bind (TM2.step (program m hm)))^[n+1] (some (cfg m 2 [] (unary n) d r p)) =
      some (halt m hm (if p && decide (r.val=1) then true::(unary n++d)
        else false::true::(unary n++d))) := by
  induction n generalizing d with
  | zero => simpa [unary] using restore_nil m hm r p d
  | succ n ih =>
      rw [unary_succ,Function.iterate_succ_apply]
      simp only [Option.bind_some,restore_cons]
      rw [ih]
      simp [unary_append_cons,unary_succ]

/-- Mathematical flag/payload specification, never a machine callback. -/
def updateBits (m : ℕ) (p : Bool) (q : ℕ) : List Bool :=
  if p && decide (q%m=1) then true::unary q else false::unary (q+1)

theorem run_update (m : ℕ) (hm : 0 < m) (p : Bool) (q : ℕ) :
    (fun c => c.bind (TM2.step (program m hm)))^[2*q+3]
      (some (cfg m 0 (p::unary q) [] [] ⟨0,hm⟩ false)) =
      some (halt m hm (updateBits m p q)) := by
  rw [show 2*q+3=(2*q+2)+1 by omega,Function.iterate_succ_apply]
  simp only [Option.bind_some,read_flag]
  rw [show 2*q+2=((q+1)+1)+q by omega,Function.iterate_add_apply,scan_run,
    Function.iterate_succ_apply]
  simp only [Option.bind_some,scan_nil,List.append_nil]
  rw [restore_run]
  simp [after,updateBits,unary_succ]

theorem init_eq (m : ℕ) (hm : 0 < m) (p : Bool) (q : ℕ) :
    (machine m hm).init (p::unary q) = cfg m 0 (p::unary q) [] [] ⟨0,hm⟩ false := by
  simp [Machine.init,machine,cfg,reset,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

theorem halt_eq (m : ℕ) (hm : 0 < m) (d : List Bool) : (machine m hm).halt d = halt m hm d := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]

/-- Exact whole updater execution, including flag read, restore, halt and reset. -/
def updateExec (m : ℕ) (hm : 0 < m) (p : Bool) (q : ℕ) :
    EvalsToInTime (TM2.step (machine m hm).program) ((machine m hm).init (p::unary q))
      (some ((machine m hm).halt (updateBits m p q))) (2*q+3) := by
  refine ⟨⟨2*q+3,?_⟩,le_refl _⟩
  exact (init_eq m hm p q).symm ▸ (halt_eq m hm (updateBits m p q)).symm ▸ run_update m hm p q

/-- Real retained primality output followed by the real residue updater. -/
def candidateMachine (m : ℕ) (hm : 0 < m) : Machine :=
  Composition.machine (RetainedInput.machine PrimeLoop.unaryMachine) (machine m hm)

def candidateBits (m q : ℕ) : List Bool := updateBits m (decide q.Prime) q

/-- Derived quartic body time in unary candidate length. -/
noncomputable def candidateTime : Polynomial ℕ := PrimeLoop.unaryTime+Polynomial.C 7*Polynomial.X+Polynomial.C 15

/-- The prime/congruence flag is obtained by actual machine composition. -/
noncomputable def candidateExec (m : ℕ) (hm : 0 < m) (q : ℕ) (hq : 2≤q) :
    EvalsToInTime (TM2.step (candidateMachine m hm).program) ((candidateMachine m hm).init (unary q))
      (some ((candidateMachine m hm).halt (candidateBits m q))) (candidateTime.eval (unary q).length) := by
  have hR := RetainedInput.executes PrimeLoop.unaryMachine (unary q) [decide q.Prime]
    (PrimeLoop.unaryTime.eval (unary q).length) (PrimeLoop.unaryExec q hq)
  have hU := updateExec m hm (decide q.Prime) q
  have h := Composition.executes (RetainedInput.machine PrimeLoop.unaryMachine) (machine m hm)
    (unary q) (decide q.Prime::unary q) (candidateBits m q) _ _ hR hU
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simp only [candidateTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,List.length_cons,List.length_nil,unary_length]
  omega

theorem candidate_input_ne_output (m : ℕ) (hm : 0 < m) :
    (candidateMachine m hm).input ≠ (candidateMachine m hm).output := by
  simp [candidateMachine,Composition.machine]

/-- Standard certificate on faithfully encoded candidates at least two. -/
noncomputable def candidateComputableInPolyTime (m : ℕ) (hm : 0 < m) :
    TM2ComputableInPolyTime PrimeLoop.unaryInput id (fun q => candidateBits m q.val) where
  tm := (candidateMachine m hm).toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := candidateTime
  outputsFun := fun q => by
    change TM2OutputsInTime (candidateMachine m hm).toFinTM2 (List.map id (PrimeLoop.unaryInput q))
      (some (List.map id (candidateBits m q.val))) (candidateTime.eval (PrimeLoop.unaryInput q).length)
    have h := Machine.outputsInTime _ _ _ _ (candidateExec m hm q.val q.property)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,PrimeLoop.unaryInput] using h


/-- The source-compatible prime/congruence test, used only as specification. -/
def Eligible (m q : ℕ) : Prop := q.Prime ∧ q%m=1
instance (m q : ℕ) : Decidable (Eligible m q) := inferInstanceAs (Decidable (_ ∧ _))

theorem candidateBits_true (m q : ℕ) (h : Eligible m q) :
    candidateBits m q=true::unary q := by
  simp [candidateBits,updateBits,h.1,h.2]

theorem candidateBits_false (m q : ℕ) (h : ¬Eligible m q) :
    candidateBits m q=false::unary (q+1) := by
  simp only [candidateBits,updateBits]
  have hg : (decide q.Prime && decide (q%m=1))=false := by
    apply Bool.eq_false_iff.mpr
    simpa [Eligible] using h
  simp [hg]

/-- Actual flag-driven repetition of the candidate program. -/
def searchMachine (m : ℕ) (hm : 0 < m) : Machine := FlagLoop.machine (candidateMachine m hm)
/-- Uniform body plus actual flag-transfer budget at a candidate. -/
noncomputable def callTime : Polynomial ℕ := candidateTime+Polynomial.C 2*Polynomial.X+Polynomial.C 6

noncomputable def stopExec (m : ℕ) (hm : 0 < m) (q : ℕ) (hq : 2≤q) (he : Eligible m q) :
    EvalsToInTime (TM2.step (searchMachine m hm).program) ((searchMachine m hm).init (unary q))
      (some ((searchMachine m hm).halt (unary q))) (callTime.eval q) := by
  have hA := candidateExec m hm q hq
  rw [candidateBits_true m q he] at hA
  have h := FlagLoop.invocationExec (candidateMachine m hm) (candidate_input_ne_output m hm)
    (unary q) (unary q) true _ hA
  simp only [FlagLoop.target] at h
  refine {h with steps_le_m := h.steps_le_m.trans ?_}
  simp only [callTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,unary_length]
  omega

noncomputable def advanceExec (m : ℕ) (hm : 0 < m) (q : ℕ) (hq : 2≤q) (he : ¬Eligible m q) :
    EvalsToInTime (TM2.step (searchMachine m hm).program) ((searchMachine m hm).init (unary q))
      (some ((searchMachine m hm).init (unary (q+1)))) (callTime.eval q) := by
  have hA := candidateExec m hm q hq
  rw [candidateBits_false m q he] at hA
  have h := FlagLoop.invocationExec (candidateMachine m hm) (candidate_input_ne_output m hm)
    (unary q) (unary (q+1)) false _ hA
  simp only [FlagLoop.target] at h
  refine {h with steps_le_m := h.steps_le_m.trans ?_}
  simp only [callTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,unary_length]
  omega

/-- Actual complete search, derived by a rank decreasing at every real continuation. -/
noncomputable def searchExec (m : ℕ) (hm : 0 < m) (q goal : ℕ) (hq : 2≤q) (hqg : q≤goal)
    (hg : Eligible m goal) (hmin : ∀ n, q≤n → n<goal → ¬Eligible m n) :
    EvalsToInTime (TM2.step (searchMachine m hm).program) ((searchMachine m hm).init (unary q))
      (some ((searchMachine m hm).halt (unary goal))) ((goal-q+1)*callTime.eval goal) := by
  suffices h : ∀ r q, goal-q=r → 2≤q → q≤goal →
      (∀ n, q≤n → n<goal → ¬Eligible m n) →
      EvalsToInTime (TM2.step (searchMachine m hm).program) ((searchMachine m hm).init (unary q))
        (some ((searchMachine m hm).halt (unary goal))) ((r+1)*callTime.eval goal) by
    exact h _ q rfl hq hqg hmin
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
      intro q hr hq hqg hmin
      by_cases he : q=goal
      · subst q
        have h := stopExec m hm goal hq hg
        refine {h with steps_le_m := h.steps_le_m.trans ?_}
        exact Nat.le_mul_of_pos_left _ (by omega)
      · have hlt : q<goal := by omega
        have ht := ih (goal-(q+1)) (by omega) (q+1) rfl (by omega) (by omega)
          (fun n hn hng => hmin n (by omega) hng)
        have hs := advanceExec m hm q hq (hmin q (le_refl _) hlt)
        have hc := Composition.polynomial_eval_monotone callTime hqg
        change callTime.eval q≤callTime.eval goal at hc
        have hs' : EvalsToInTime (TM2.step (searchMachine m hm).program)
            ((searchMachine m hm).init (unary q))
            (some ((searchMachine m hm).init (unary (q+1)))) (callTime.eval goal) :=
          {hs with steps_le_m := hs.steps_le_m.trans hc}
        have h := EvalsToInTime.trans (TM2.step (searchMachine m hm).program)
          (callTime.eval goal) ((goal-(q+1)+1)*callTime.eval goal)
          _ _ _ hs' ht
        refine {h with steps_le_m := h.steps_le_m.trans ?_}
        have hc' : (goal-(q+1)+1)*callTime.eval goal+callTime.eval goal=
            (goal-(q+1)+2)*callTime.eval goal := by ring
        rw [hc']
        have he' : goal-(q+1)+2=r+1 := by omega
        rw [he']

/-- Quintic selected-output budget for the complete candidate loop. -/
noncomputable def searchTime : Polynomial ℕ := (Polynomial.X+1)*callTime

/-- The bound is polynomial in the selected output, not assumed polynomial in the input bound. -/
noncomputable def searchPolyExec (m : ℕ) (hm : 0 < m) (q goal : ℕ) (hq : 2≤q) (hqg : q≤goal)
    (hg : Eligible m goal) (hmin : ∀ n, q≤n → n<goal → ¬Eligible m n) :
    EvalsToInTime (TM2.step (searchMachine m hm).program) ((searchMachine m hm).init (unary q))
      (some ((searchMachine m hm).halt (unary goal))) (searchTime.eval goal) := by
  have h := searchExec m hm q goal hq hqg hg hmin
  refine {h with steps_le_m := h.steps_le_m.trans ?_}
  simpa only [searchTime,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_one] using Nat.mul_le_mul_right (callTime.eval goal) (show goal-q+1≤goal+1 by omega)


/-- Actual lower-bound writer followed by the real eligible-prime scan. -/
def fullMachine (m : ℕ) (hm : 0 < m) : Machine :=
  Composition.machine (LowerBound.machine m) (searchMachine m hm)

/-- Derived selected-output budget including actual lower-bound initialization. -/
noncomputable def fullTime : Polynomial ℕ := searchTime+Polynomial.C 4*Polynomial.X+Polynomial.C 5

/-- Complete execution from the requested bound, preserving the least eligible output. -/
noncomputable def fullExec (m : ℕ) (hm : 0 < m) (B goal : ℕ) (hBound : max B m<goal)
    (hg : Eligible m goal) (hmin : ∀ n, max B m<n → n<goal → ¬Eligible m n) :
    EvalsToInTime (TM2.step (fullMachine m hm).program) ((fullMachine m hm).init (unary B))
      (some ((fullMachine m hm).halt (unary goal))) (fullTime.eval goal) := by
  have hL := LowerBound.executes m B
  have hS := searchPolyExec m hm (max B m+1) goal (by have := Nat.le_max_right B m;omega)
    (by omega) hg (fun n hn hng => hmin n (by omega) hng)
  have h := Composition.executes (LowerBound.machine m) (searchMachine m hm)
    (unary B) (unary (max B m+1)) (unary goal) _ _ hL hS
  refine {h with steps_le_m := h.steps_le_m.trans ?_}
  simp only [fullTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,unary_length]
  have := Nat.le_max_left B m
  omega

theorem fullTime_eval (n : ℕ) : fullTime.eval n =
    (n+1)*(((n+6)^2+1)*(5*(3*(n+6)+3)^2+27*(n+6)+41)+2*(n+6)+3+9*n+21)+4*n+5 := by
  simp only [fullTime,searchTime,callTime,candidateTime,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,PrimeLoop.unaryTime_eval]
  ring

end QEC.Coding.BitTuring.UnaryArithmetic.ResiduePrime
