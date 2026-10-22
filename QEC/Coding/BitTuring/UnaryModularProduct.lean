import QEC.Coding.BitTuring.UnaryRemainder
import QEC.Coding.BitTuring.UnaryFactorTest

/-!
# Actual unary modular product with a variable tape modulus

One fixed seven-stack, fourteen-label Boolean machine parses a faithful unary triple `(a,b,q)`,
retains the positive modulus on tape, executes the proved multiplication instructions, and
enters the actual remainder loop directly from the product tape. Every lifted instruction and
both handoffs are proved. The complete halt has only unary `(a*b)%q` on the output tape and
reset finite variables. No natural data, multiplication, modulo or cost callback resides in
finite control; the existing arithmetic instructions themselves execute.

The actual label count is `(a+1)*(2*b+4)+2*q+2+(a*b/q)*(2*q+2)`, at most `8*(L+1)^2` for
unary encoded input length `L`. Standard Mathlib polynomial-time and canonical ZMod product
and square output certificates derive from that execution. This is unary input time, not
binary natural-number time or the complete explicit PK22 runtime. Boolean is an encoding
alphabet, with no restriction on the quantum-code field.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularProduct
open Turing StateTransition
/-- Seven Boolean tapes: multiplication working tapes, retained modulus and fresh output. -/
abbrev Stack := Fin 5 ⊕ Fin 2
/-- Fourteen finite labels for actual triple parsing, multiplication and remainder. -/
abbrev Label := Fin 3 ⊕ (Fin 6 ⊕ Fin 5)
/-- Embed original multiplication labels in the combined finite control. -/
def mulLabel (l : Fin 6) : Label := .inr (.inl l)
/-- Embed original remainder labels in the combined finite control. -/
def remLabel (l : Fin 5) : Label := .inr (.inr l)
/-- Route remainder input, numerator, modulus and output to the actual seven tapes. -/
def remStack (k : Fin 4) : Stack :=
  if k=0 then .inl 0 else if k=1 then .inl 4 else if k=2 then .inr 0 else .inr 1

/-- Concrete triple parser and lifted arithmetic instructions; no semantic callback. -/
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .inl 0 => .pop (.inl 0) (fun _ h => h)
      (.branch (fun v => v.getD false)
        (.push (.inl 1) (fun _ => true) (.goto fun _ => .inl 0)) (.goto fun _ => .inl 1))
  | .inl 1 => .pop (.inl 0) (fun _ h => h)
      (.branch (fun v => v.getD false)
        (.push (.inl 2) (fun _ => true) (.goto fun _ => .inl 1)) (.goto fun _ => .inl 2))
  | .inl _ => .pop (.inl 0) (fun _ h => h)
      (.branch Option.isSome
        (.push (.inr 0) (fun v => v.getD false) (.goto fun _ => .inl 2))
        (.goto fun _ => mulLabel 2))
  | .inr (.inl l) => liftStatement Sum.inl mulLabel id (fun _ w => w)
      (some (remLabel 2)) (multiplicationProgram l)
  | .inr (.inr l) => liftStatement remStack remLabel id (fun _ w => w)
      none (Remainder.program l)

/-- One fixed finite machine independent of both operands and the dynamic modulus. -/
def machine : Machine where
  K := Stack
  input := .inl 0
  output := .inr 1
  Λ := Label
  main := .inl 0
  σ := Option Bool
  initial := none
  program := program

/-- Complete actual parser configuration with retained modulus and empty output. -/
def prefixCfg (phase : Fin 3) (source a b q : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  ⟨some (.inl phase),v,fun k => match k with
    | .inl k => ![source,a,b,[],[]] k
    | .inr k => ![q,[]] k⟩
/-- Embed multiplication tapes while preserving the separate tape modulus. -/
def mulTapes (q : List Bool) (S : Fin 5 → List Bool) : Stack → List Bool
  | .inl k => S k
  | .inr k => if k = 0 then q else []

/-- Embed a multiplication configuration and redirect its actual halt to remainder. -/
def embedMul (q : List Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) →
    TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  liftCfg mulLabel id (mulTapes q) (some (remLabel 2))

/-- Real multiplication updates preserve the separate dynamic modulus. -/
theorem mulTapes_update (q : List Bool) (S : Fin 5 → List Bool) (k : Fin 5) (w : List Bool) :
    Function.update (mulTapes q S) (.inl k) w = mulTapes q (Function.update S k w) := by
  funext j
  cases j with
  | inl j => by_cases h : j = k <;> simp [mulTapes,h]
  | inr j => simp [mulTapes]

/-- Each lifted multiplication instruction has its original concrete semantics. -/
theorem stepAuxMul (q : List Bool) (l : Fin 6) (v : Option Bool) (S : Fin 5 → List Bool) :
    TM2.stepAux (program (mulLabel l)) v (mulTapes q S) =
      embedMul q (TM2.stepAux (multiplicationProgram l) v S) :=
  stepAux_liftStatement (K := Fin 5) (K' := Stack) (Λ := Fin 6) (Λ' := Label)
    (σ := Option Bool) (σ' := Option Bool) Sum.inl mulLabel id (fun _ w => w)
    (some (remLabel 2)) id (mulTapes q) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (mulTapes_update q) (multiplicationProgram l) v S

/-- Successful multiplication steps lift to actual combined-machine steps. -/
theorem stepMul (q : List Bool)
    (c c' : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool))
    (h : TM2.step multiplicationProgram c = some c') :
    TM2.step program (embedMul q c) = some (embedMul q c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (multiplicationProgram l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAuxMul q l v S)

/-- Transfer one first-operand bit to its actual working tape. -/
theorem parseA_cons (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 0 (true :: s) a b q v) =
      some (prefixCfg 0 s (true :: a) b q (some true)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- Consume the first delimiter and enter second-operand parsing. -/
theorem parseA_sep (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 0 (false :: s) a b q v) =
      some (prefixCfg 1 s a b q (some false)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- Transfer one second-operand bit to its actual working tape. -/
theorem parseB_cons (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 1 (true :: s) a b q v) =
      some (prefixCfg 1 s a (true :: b) q (some true)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- Consume the second delimiter and enter dynamic-modulus parsing. -/
theorem parseB_sep (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 1 (false :: s) a b q v) =
      some (prefixCfg 2 s a b q (some false)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- Retain one modulus bit on its independent tape. -/
theorem parseQ_cons (x : Bool) (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 2 (x :: s) a b q v) =
      some (prefixCfg 2 s a b (x :: q) (some x)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- Complete parsing, reset variables and enter the multiplication loop. -/
theorem parseQ_nil (a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 2 [] a b q v) =
      some (embedMul q (multiplicationCfg 2 [] a b [] [] none)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq,embedMul,liftCfg,
    multiplicationCfg,mulLabel]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [mulTapes,Function.update]
  | inr k => fin_cases k <;> simp [mulTapes,Function.update]

/-- Counted complete first-operand parsing including its delimiter. -/
theorem run_parseA (n : ℕ) (s a b q : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n + 1]
      (some (prefixCfg 0 (unary n ++ false :: s) a b q v)) =
      some (prefixCfg 1 s (unary n ++ a) b q (some false)) := by
  induction n generalizing a v with
  | zero => simp [parseA_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,parseA_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: a) (some true)

/-- Counted complete second-operand parsing including its delimiter. -/
theorem run_parseB (n : ℕ) (s a b q : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n + 1]
      (some (prefixCfg 1 (unary n ++ false :: s) a b q v)) =
      some (prefixCfg 2 s a (unary n ++ b) q (some false)) := by
  induction n generalizing b v with
  | zero => simp [parseB_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,parseB_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: b) (some true)

/-- Counted complete modulus parsing with exact multiplication handoff. -/
theorem run_parseQ (n : ℕ) (a b q : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n + 1]
      (some (prefixCfg 2 (unary n) a b q v)) =
      some (embedMul (unary n ++ q) (multiplicationCfg 2 [] a b [] [] none)) := by
  induction n generalizing q v with
  | zero => simp [parseQ_nil]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,parseQ_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: q) (some true)

/-- The faithful triple is actually parsed into independent operand and modulus tapes. -/
theorem run_prefix (a b q : ℕ) :
    (fun c => c.bind (TM2.step program))^[a + b + q + 3]
      (some (prefixCfg 0 (FactorTest.tripleInput a b q) [] [] [] none)) =
      some (embedMul (unary q) (multiplicationCfg 2 [] (unary a) (unary b) [] [] none)) := by
  rw [show a + b + q + 3 = ((q + 1) + (b + 1)) + (a + 1) by omega,
    Function.iterate_add_apply]
  simp only [FactorTest.tripleInput,pairInput]
  rw [run_parseA]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply,run_parseB]
  simp only [List.append_nil]
  simpa only [List.append_nil] using run_parseQ q (unary a) (unary b) [] (some false)

/-- Execute the actual counted multiplication loop while preserving the tape modulus. -/
theorem run_mul (a b q : ℕ) :
    (fun c => c.bind (TM2.step program))^[a * (2 * b + 3) + b + 2]
      (some (embedMul (unary q) (multiplicationCfg 2 [] (unary a) (unary b) [] [] none))) =
      some (embedMul (unary q) (multiplicationHalt (unary (a * b)))) := by
  have hm := QEC.Coding.BitTuring.UnaryArithmetic.run_outer a b [] none
  simp only [List.append_nil] at hm
  exact iterate_lift (TM2.step multiplicationProgram) (TM2.step program) (embedMul (unary q))
    (stepMul (unary q)) _ _ _ hm


/-- Embed remainder tapes with every unused multiplication tape empty. -/
def remTapes (S : Fin 4 → List Bool) : Stack → List Bool
  | .inl k => if k=0 then S 0 else if k=4 then S 1 else []
  | .inr k => if k=0 then S 2 else S 3

/-- Embed a whole remainder configuration with its genuine halt preserved. -/
def embedRem : TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool) →
    TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  liftCfg remLabel id remTapes none

/-- Remainder stack routing reads the exact original tape. -/
theorem remTapes_read (S : Fin 4 → List Bool) (k : Fin 4) :
    remTapes S (remStack k)=S k := by
  fin_cases k <;> simp [remTapes,remStack]

/-- Remainder stack updates commute with the complete tape embedding. -/
theorem remTapes_update (S : Fin 4 → List Bool) (k : Fin 4) (w : List Bool) :
    Function.update (remTapes S) (remStack k) w=remTapes (Function.update S k w) := by
  funext j
  cases j with
  | inl j => fin_cases k <;> fin_cases j <;> simp [remTapes,remStack,Function.update]
  | inr j => fin_cases k <;> fin_cases j <;> simp [remTapes,remStack,Function.update]

/-- Each lifted remainder instruction preserves its original concrete semantics. -/
theorem stepAuxRem (l : Fin 5) (v : Option Bool) (S : Fin 4 → List Bool) :
    TM2.stepAux (program (remLabel l)) v (remTapes S)=
      embedRem (TM2.stepAux (Remainder.program l) v S) :=
  stepAux_liftStatement (K:=Fin 4) (K':=Stack) (Λ:=Fin 5) (Λ':=Label)
    (σ:=Option Bool) (σ':=Option Bool) remStack remLabel id (fun _ w => w)
    none id remTapes (fun _ => rfl) (fun _ _ => rfl)
    remTapes_read remTapes_update (Remainder.program l) v S

/-- Successful remainder steps lift to actual combined-machine steps. -/
theorem stepRem (c c' : TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool))
    (h : TM2.step Remainder.program c=some c') :
    TM2.step program (embedRem c)=some (embedRem c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (Remainder.program l) v S=c' := Option.some.inj h
      rw [←hh]
      exact congrArg some (stepAuxRem l v S)

/-- The actual multiplication halt is exactly the remainder-loop initial configuration. -/
theorem handoff (n q : ℕ) :
    embedMul (unary q) (multiplicationHalt (unary n))=
      embedRem (Remainder.cfg 2 [] (unary n) (unary q) [] none) := by
  simp [embedMul,embedRem,liftCfg,multiplicationHalt,Remainder.cfg,
    mulLabel,remLabel,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [mulTapes,remTapes]
  | inr k => fin_cases k <;> simp [mulTapes,remTapes]

/-- Complete clean halt with only the modular-product output tape populated. -/
def finalHalt (w : List Bool) : TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  ⟨none,none,Function.update (fun _ => []) (.inr 1) w⟩

/-- The genuine embedded remainder halt is the full clean combined-machine halt. -/
theorem embedRem_halt (w : List Bool) : embedRem (Remainder.halt w)=finalHalt w := by
  simp [embedRem,liftCfg,Remainder.halt,finalHalt,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [remTapes,Function.update]
  | inr k => fin_cases k <;> simp [remTapes,Function.update]

/-- Execute the actual counted remainder loop and drain every non-output tape. -/
theorem run_rem (n q : ℕ) (hq : 0<q) :
    (fun c => c.bind (TM2.step program))^[n/q*(2*q+2)+q+1]
      (some (embedRem (Remainder.cfg 2 [] (unary n) (unary q) [] none)))=
      some (finalHalt (unary (n%q))) := by
  have h := iterate_lift (TM2.step Remainder.program) (TM2.step program)
    embedRem stepRem _ _ _ (Remainder.run_body n q hq none)
  rw [embedRem_halt] at h
  simpa only [Nat.add_assoc] using h

/-- Full label-step count including parsing, multiplication, remainder and cleanup. -/
def steps (a b q : ℕ) := (a+1)*(2*b+4)+2*q+2+(a*b/q)*(2*q+2)

/-- Actual complete execution computes the modular product and cleanly halts. -/
theorem run (a b q : ℕ) (hq : 0<q) :
    (fun c => c.bind (TM2.step program))^[steps a b q]
      (some (prefixCfg 0 (FactorTest.tripleInput a b q) [] [] [] none))=
      some (finalHalt (unary ((a*b)%q))) := by
  have ht : steps a b q=((a*b/q*(2*q+2)+q+1)+(a*(2*b+3)+b+2))+(a+b+q+3) := by
    unfold steps
    ring
  rw [ht,Function.iterate_add_apply,run_prefix,Function.iterate_add_apply,run_mul,handoff]
  exact run_rem (a*b) q hq

/-- The standard machine initialization equals the complete concrete parser entry. -/
theorem init_eq (a b q : ℕ) :
    machine.init (FactorTest.tripleInput a b q)=
      prefixCfg 0 (FactorTest.tripleInput a b q) [] [] [] none := by
  simp [Machine.init,machine,prefixCfg,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- The standard machine halt equals the concrete clean output configuration. -/
theorem halt_eq (w : List Bool) : machine.halt w=finalHalt w := by rfl

/-- Counted standard execution derived from the actual complete instruction run. -/
def exec (a b q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a b q))
      (some (machine.halt (unary ((a*b)%q)))) (steps a b q) := by
  refine ⟨⟨steps a b q,?_⟩,le_refl _⟩
  rw [init_eq,halt_eq]
  exact run a b q hq

/-- The actual cancellation/restoration loop budget is at most four times the numerator. -/
theorem quotient_steps_le (n q : ℕ) : n/q*(2*q+2)≤4*n := by
  calc
    n/q*(2*q+2)=2*(n/q*q)+2*(n/q) := by ring
    _≤2*n+2*n := Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.div_mul_le_self n q))
      (Nat.mul_le_mul_left 2 (Nat.div_le_self n q))
    _=4*n := by ring

/-- Complete execution is quadratic in the faithful unary encoded-input length. -/
theorem steps_le (a b q : ℕ) :
    steps a b q≤8*((FactorTest.tripleInput a b q).length+1)^2 := by
  let L := (FactorTest.tripleInput a b q).length+1
  have hL : L=a+b+q+3 := by dsimp [L];rw [FactorTest.tripleInput_length]
  have hp : (pairInput a b).length+1≤L := by rw [pairInput_length,hL];omega
  have hm : (a+1)*(2*b+4)≤2*L^2 :=
    (multiplication_steps_le a b).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hp 2))
  have hab : a*b≤L^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega : a≤L) (by omega : b≤L)
  have hq : q+1≤L^2 := by
    have hl : 1≤L := by omega
    have hll : L≤L^2 := by simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left L hl
    exact (by omega : q+1≤L).trans hll
  have hd := (quotient_steps_le (a*b) q).trans (Nat.mul_le_mul_left 4 hab)
  change steps a b q≤8*L^2
  unfold steps
  omega

/-- The quadratic mathematical polynomial bounding the actual counted execution. -/
noncomputable def time : Polynomial ℕ := Polynomial.C 8*(Polynomial.X+1)^2
/-- The genuine full execution fits the quadratic encoded-input time polynomial. -/
noncomputable def polyExec (a b q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a b q))
      (some (machine.halt (unary ((a*b)%q)))) (time.eval (FactorTest.tripleInput a b q).length) := by
  have h := exec a b q hq
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simpa [time] using steps_le a b q

/-- Standard Mathlib output certificate for the actual modular-product machine. -/
noncomputable def outputsInTime (a b q : ℕ) (hq : 0<q) :
    TM2OutputsInTime machine.toFinTM2 (FactorTest.tripleInput a b q)
      (some (unary ((a*b)%q))) (time.eval (FactorTest.tripleInput a b q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec a b q hq)

/-- The actual output is the canonical value of the genuine ZMod product. -/
noncomputable def outputsZModProductInTime (a b q : ℕ) (hq : 0<q) :
    TM2OutputsInTime machine.toFinTM2 (FactorTest.tripleInput a b q)
      (some (unary (((a:ZMod q)*(b:ZMod q)).val)))
      (time.eval (FactorTest.tripleInput a b q).length) := by
  let : NeZero q := ⟨hq.ne'⟩
  simpa only [←Nat.cast_mul,ZMod.val_natCast] using outputsInTime a b q hq

/-- Duplicated operands give the canonical value of the genuine ZMod square. -/
noncomputable def outputsZModSquareInTime (a q : ℕ) (hq : 0<q) :
    TM2OutputsInTime machine.toFinTM2 (FactorTest.tripleInput a a q)
      (some (unary (((a:ZMod q)^2).val)))
      (time.eval (FactorTest.tripleInput a a q).length) := by
  simpa only [pow_two] using outputsZModProductInTime a a q hq

/-- Faithful unary triple encoding for two naturals and a positive dynamic modulus. -/
def input (x : ℕ×(ℕ×ℕ+)) : List Bool := FactorTest.tripleInput x.1 x.2.1 x.2.2.val

/-- The positive-modulus triple encoding distinguishes every valid input. -/
theorem input_injective : Function.Injective input := by
  intro x y h
  have he := @FactorTest.tripleInput_injective (x.1,(x.2.1,x.2.2.val)) (y.1,(y.2.1,y.2.2.val)) h
  have ha : x.1=y.1 := congrArg (fun z:ℕ×(ℕ×ℕ) => z.1) he
  have hb : x.2.1=y.2.1 := congrArg (fun z:ℕ×(ℕ×ℕ) => z.2.1) he
  have hq : x.2.2.val=y.2.2.val := congrArg (fun z:ℕ×(ℕ×ℕ) => z.2.2) he
  exact Prod.ext ha (Prod.ext hb (Subtype.ext hq))

/-- Standard polynomial-time modular product using the actual fixed machine. -/
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary
    (fun x:ℕ×(ℕ×ℕ+) => (x.1*x.2.1)%x.2.2.val) where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun x => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary ((x.1*x.2.1)%x.2.2.val)))) (time.eval (input x).length)
    have h := outputsInTime x.1 x.2.1 x.2.2.val x.2.2.pos
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input] using h

end QEC.Coding.BitTuring.UnaryArithmetic.ModularProduct
