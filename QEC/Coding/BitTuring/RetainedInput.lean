import QEC.Coding.BitTuring.Composition

/-!
# Actual Boolean Turing-machine execution retaining the original input

Five fresh Boolean stacks and six fresh labels duplicate the input, restore the body copy,
run the actual body while preserving a reversed backup, restore that backup and prepend the
actual result through the proved two-phase copy instructions. Real finish resets all finite
variables and halts with only the final output `y ++ x` populated. Body input and output
may be the same stack.

An independently proved body execution within a steps yields actual combined execution
within `a+3*|x|+2*|y|+6`. Actual output-stack growth derives a natural time polynomial and
a standard Mathlib certificate for valid encoded inputs. Semantic functions, time bounds
and polynomials never execute inside the finite machine or inhabit correctness/cost fields.

This closure permits trial-factor and comparison results to retain their original records;
it does not supply their counter-update/prime-scan programs, whole PK22 block-size runtime
or unconditional spectral theorem. Boolean is the tape encoding alphabet.
-/

namespace QEC.Coding.BitTuring.RetainedInput
open Turing StateTransition
variable (A : Machine)

/-- Body stacks plus incoming input, reversed input copies, output-copy buffer and final output. -/
abbrev Stack := A.K ⊕ Fin 5
/-- Body labels plus actual duplication, restoration, copying and finish controls. -/
abbrev Label := A.Λ ⊕ Fin 6
/-- Body finite variables and a finite current-head Option-Bool. -/
abbrev Var := A.σ × Option Bool

/-- Embed body tapes while retaining the reversed original input in a fresh stack. -/
def tapes (q : List Bool) (S : A.K → List Bool) : Stack A → List Bool
  | .inl k => S k
  | .inr k => if k = 2 then q else []

/-- Embed the body configuration, redirecting halt to actual backup restoration. -/
def embed (q : List Bool) : A.Cfg → TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  liftCfg Sum.inl (fun v => (v,none)) (tapes A q) (some (.inr 2))

/-- Route the original output through a fresh buffer to the fresh final output. -/
def copyStack (k : Fin 3) : Stack A :=
  if k = 0 then .inl A.output else if k = 1 then .inr 3 else .inr 4

/-- Embed complete copy tapes; all other body and fresh stacks are empty. -/
def copyTapes (S : Fin 3 → List Bool) : Stack A → List Bool
  | .inl k => if k = A.output then S 0 else []
  | .inr k => if k = 3 then S 1 else if k = 4 then S 2 else []

/-- Map the two actual copy phases into the compiler controls. -/
def copyLabel (phase : Bool) : Label A := .inr (if phase then 3 else 4)

/-- Embed the real copy configuration and redirect halt to variable reset. -/
def embedCopy : TM2.Cfg (fun _ : Fin 3 => Bool) Bool (Option Bool) →
    TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  liftCfg (copyLabel A) (fun v => (A.initial,v)) (copyTapes A) (some (.inr 5))

/-- Actual duplication, restoration, body, copying and finish instructions; no semantic callback. -/
def program : Label A → TM2.Stmt (fun _ : Stack A => Bool) (Label A) (Var A)
  | .inl l => liftStatement Sum.inl Sum.inl Prod.fst (fun v w => (w,v.2))
      (some (.inr 2)) (A.program l)
  | .inr 0 => .pop (.inr 0) (fun v h => (v.1,h))
      (.branch (fun v => v.2.isSome)
        (.push (.inr 1) (fun v => v.2.getD false)
          (.push (.inr 2) (fun v => v.2.getD false) (.goto fun _ => .inr 0)))
        (.goto fun _ => .inr 1))
  | .inr 1 => .pop (.inr 1) (fun v h => (v.1,h))
      (.branch (fun v => v.2.isSome)
        (.push (.inl A.input) (fun v => v.2.getD false) (.goto fun _ => .inr 1))
        (.load (fun _ => (A.initial,none)) (.goto fun _ => .inl A.main)))
  | .inr 2 => .pop (.inr 2) (fun v h => (v.1,h))
      (.branch (fun v => v.2.isSome)
        (.push (.inr 4) (fun v => v.2.getD false) (.goto fun _ => .inr 2))
        (.load (fun _ => (A.initial,none)) (.goto fun _ => .inr 3)))
  | .inr 3 => liftStatement (copyStack A) (copyLabel A) Prod.snd
      (fun v h => (v.1,h)) (some (.inr 5)) (copyProgram true)
  | .inr 4 => liftStatement (copyStack A) (copyLabel A) Prod.snd
      (fun v h => (v.1,h)) (some (.inr 5)) (copyProgram false)
  | .inr _ => .load (fun _ => (A.initial,none)) .halt

/-- Construct the finite Boolean machine before assuming any execution or runtime property. -/
def machine : Machine where
  K := Stack A
  input := .inr 0
  output := .inr 4
  Λ := Label A
  main := .inr 0
  σ := Var A
  initial := (A.initial,none)
  program := program A

/-- Complete duplicate/restore configuration with a separate body input stack. -/
def preCfg (phase : Fin 6) (s buf q d : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  ⟨some (.inr phase), (A.initial,v), fun k => match k with
    | .inl k => if k = A.input then d else []
    | .inr k => ![s,buf,q,[],[]] k⟩

/-- Complete backup-restoration configuration with the actual body output preserved. -/
def postCfg (y q d : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  ⟨some (.inr 2), (A.initial,v), fun k => match k with
    | .inl k => if k = A.output then y else []
    | .inr k => ![[],[],q,[],d] k⟩

/-- Body updates commute with the backup-preserving disjoint tape embedding. -/
theorem tapes_update (q : List Bool) (S : A.K → List Bool) (k : A.K) (w : List Bool) :
    Function.update (tapes A q S) (.inl k) w = tapes A q (Function.update S k w) := by
  funext j
  cases j with
  | inl j => by_cases h : j = k <;> simp [tapes,h]
  | inr j => simp [tapes]

/-- Every actual lifted body instruction has its original semantics. -/
theorem stepAux (q : List Bool) (l : A.Λ) (v : A.σ) (S : A.K → List Bool) :
    TM2.stepAux (program A (.inl l)) (v,none) (tapes A q S) =
      embed A q (TM2.stepAux (A.program l) v S) :=
  stepAux_liftStatement (K := A.K) (K' := Stack A) (Λ := A.Λ) (Λ' := Label A)
    (σ := A.σ) (σ' := Var A) Sum.inl Sum.inl Prod.fst (fun v w => (w,v.2))
    (some (.inr 2)) (fun v => (v,none)) (tapes A q)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (tapes_update A q) (A.program l) v S

/-- Each successful body step is one real compiler-machine step. -/
theorem step (q : List Bool) (c c' : A.Cfg) (h : TM2.step A.program c = some c') :
    TM2.step (program A) (embed A q c) = some (embed A q c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (A.program l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAux A q l v S)

/-- Actually duplicate one incoming bit into both reversed-input stacks. -/
theorem duplicate_cons (x : Bool) (s buf q d : List Bool) (v : Option Bool) :
    TM2.step (program A) (preCfg A 0 (x :: s) buf q d v) =
      some (preCfg A 0 s (x :: buf) (x :: q) d (some x)) := by
  simp [TM2.step,program,preCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- Detect the empty incoming input and enter body-input restoration. -/
theorem duplicate_nil (buf q d : List Bool) (v : Option Bool) :
    TM2.step (program A) (preCfg A 0 [] buf q d v) =
      some (preCfg A 1 [] buf q d none) := by
  simp [TM2.step,program,preCfg,TM2.stepAux,TM2.Cfg.mk.injEq]

/-- Restore one reversed body-input bit into the actual body channel. -/
theorem restore_cons (x : Bool) (s q d : List Bool) (v : Option Bool) :
    TM2.step (program A) (preCfg A 1 [] (x :: s) q d v) =
      some (preCfg A 1 [] s q (x :: d) (some x)) := by
  simp [TM2.step,program,preCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => by_cases h : k = A.input <;> simp [Function.update,h]
  | inr k => fin_cases k <;> simp [Function.update]

/-- Finish restoration, reset finite variables and enter the real body program. -/
theorem restore_nil (q d : List Bool) (v : Option Bool) :
    TM2.step (program A) (preCfg A 1 [] [] q d v) =
      some (embed A q (A.init d)) := by
  simp [TM2.step,program,preCfg,embed,liftCfg,Machine.init,TM2.stepAux,
    TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => simp [tapes,Function.update]
  | inr k => fin_cases k <;> simp [tapes]

/-- Counted duplication constructs both reversed input copies. -/
theorem duplicate_run (w buf q d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step (program A)))^[w.length + 1]
      (some (preCfg A 0 w buf q d v)) =
      some (preCfg A 1 [] (w.reverse ++ buf) (w.reverse ++ q) d none) := by
  induction w generalizing buf q v with
  | nil => simp [duplicate_nil]
  | cons x xs ih =>
      rw [List.length_cons,Nat.add_right_comm,Function.iterate_succ_apply]
      simp only [Option.bind_some,duplicate_cons]
      simpa [List.reverse_cons,List.append_assoc] using ih (x :: buf) (x :: q) (some x)

/-- Counted restoration reverses the body input copy and leaves the backup intact. -/
theorem restore_run (w q d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step (program A)))^[w.length + 1]
      (some (preCfg A 1 [] w q d v)) = some (embed A q (A.init (w.reverse ++ d))) := by
  induction w generalizing d v with
  | nil => simp [restore_nil]
  | cons x xs ih =>
      rw [List.length_cons,Nat.add_right_comm,Function.iterate_succ_apply]
      simp only [Option.bind_some,restore_cons]
      simpa [List.reverse_cons,List.append_assoc] using ih (x :: d) (some x)

/-- The complete real prefix gives the body its original input and retains a reversed backup. -/
theorem prefix_run (w : List Bool) :
    (fun c => c.bind (TM2.step (program A)))^[2 * w.length + 2]
      (some (preCfg A 0 w [] [] [] none)) = some (embed A w.reverse (A.init w)) := by
  rw [show 2 * w.length + 2 = (w.reverse.length + 1) + (w.length + 1) by simp; omega,
    Function.iterate_add_apply,duplicate_run]
  simp only [List.append_nil]
  simpa using restore_run A w.reverse w.reverse [] none

/-- Restore one backup bit into the fresh final output. -/
theorem backup_cons (x : Bool) (s y d : List Bool) (v : Option Bool) :
    TM2.step (program A) (postCfg A y (x :: s) d v) =
      some (postCfg A y s (x :: d) (some x)) := by
  simp [TM2.step,program,postCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- Finish backup restoration and enter real body-output copying. -/
theorem backup_nil (y d : List Bool) (v : Option Bool) :
    TM2.step (program A) (postCfg A y [] d v) =
      some (embedCopy A (copyCfg true y [] d none)) := by
  simp [TM2.step,program,postCfg,embedCopy,liftCfg,copyCfg,copyLabel,
    TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => simp [copyTapes,Function.update]
  | inr k => fin_cases k <;> simp [copyTapes,Function.update]

/-- Counted backup restoration preserves the real body output and restores the original order. -/
theorem backup_run (w y d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step (program A)))^[w.length + 1]
      (some (postCfg A y w d v)) =
      some (embedCopy A (copyCfg true y [] (w.reverse ++ d) none)) := by
  induction w generalizing d v with
  | nil => simp [backup_nil]
  | cons x xs ih =>
      rw [List.length_cons,Nat.add_right_comm,Function.iterate_succ_apply]
      simp only [Option.bind_some,backup_cons]
      simpa [List.reverse_cons,List.append_assoc] using ih (x :: d) (some x)

/-- The complete embedded body halt equals the actual backup-restoration entry. -/
theorem embed_halt (w y : List Bool) :
    embed A w (A.halt y) = postCfg A y w [] none := by
  simp [embed,liftCfg,Machine.halt,postCfg,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => simp [tapes,Function.update]
  | inr k => fin_cases k <;> simp [tapes]

/-- Copy reads commute with the disjoint body/fresh-stack embedding. -/
theorem copyTapes_read (S : Fin 3 → List Bool) (k : Fin 3) :
    copyTapes A S (copyStack A k) = S k := by
  fin_cases k <;> simp [copyStack,copyTapes]

/-- Copy updates commute with the complete tape embedding. -/
theorem copyTapes_update (S : Fin 3 → List Bool) (k : Fin 3) (w : List Bool) :
    Function.update (copyTapes A S) (copyStack A k) w =
      copyTapes A (Function.update S k w) := by
  fin_cases k <;> funext j
  all_goals
    cases j with
    | inl j => by_cases h : j = A.output <;> simp [copyStack,copyTapes,h]
    | inr j => fin_cases j <;> simp [copyStack,copyTapes]

/-- Both real lifted copy branches have the original instruction semantics. -/
theorem stepAuxCopy (phase : Bool) (v : Option Bool) (S : Fin 3 → List Bool) :
    TM2.stepAux (program A (copyLabel A phase)) (A.initial,v) (copyTapes A S) =
      embedCopy A (TM2.stepAux (copyProgram phase) v S) := by
  have h := stepAux_liftStatement (K := Fin 3) (K' := Stack A) (Λ := Bool) (Λ' := Label A)
    (σ := Option Bool) (σ' := Var A) (copyStack A) (copyLabel A) Prod.snd
    (fun v h => (v.1,h)) (some (.inr 5)) (fun v => (A.initial,v)) (copyTapes A)
    (fun _ => rfl) (fun _ _ => rfl) (copyTapes_read A) (copyTapes_update A)
    (copyProgram phase) v S
  cases phase <;> simpa [program,copyLabel,embedCopy] using h

/-- Each successful copy step is one real compiler-machine step. -/
theorem stepCopy (c c' : TM2.Cfg (fun _ : Fin 3 => Bool) Bool (Option Bool))
    (h : TM2.step copyProgram c = some c') :
    TM2.step (program A) (embedCopy A c) = some (embedCopy A c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (copyProgram l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAuxCopy A l v S)

/-- The original two-phase copy program prepends its source while preserving a suffix. -/
theorem copyRun_suffix (w d : List Bool) :
    (fun c => c.bind (TM2.step copyProgram))^[2 * w.length + 2]
      (some (copyCfg true w [] d none)) = some (copyHalt (w ++ d)) := by
  rw [show 2 * w.length + 2 = (w.reverse.length + 1) + (w.length + 1) by simp; omega,
    Function.iterate_add_apply,copyRun_source]
  simp only [List.append_nil]
  simpa using copyRun_buffer w.reverse d none

/-- Actually reset all finite variables and halt with every non-output stack empty. -/
theorem finish (d : List Bool) :
    TM2.step (program A) (embedCopy A (copyHalt d)) = some ((machine A).halt d) := by
  simp [TM2.step,program,embedCopy,liftCfg,copyHalt,Machine.halt,machine,
    TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => simp [copyTapes,Function.update]
  | inr k => fin_cases k <;> simp [copyTapes,Function.update]

/-- Counted post-body restoration/copy/finish prepends the actual result to original input. -/
theorem transfer (x y : List Bool) :
    (fun c => c.bind (TM2.step (program A)))^[x.length + 2 * y.length + 4]
      (some (embed A x.reverse (A.halt y))) = some ((machine A).halt (y ++ x)) := by
  rw [show x.length + 2 * y.length + 4 =
      (1 + (2 * y.length + 2)) + (x.reverse.length + 1) by simp; omega,
    Function.iterate_add_apply,embed_halt,backup_run]
  simp only [List.reverse_reverse,List.append_nil]
  rw [Function.iterate_add_apply,
    iterate_lift (TM2.step copyProgram) (TM2.step (program A)) (embedCopy A)
      (stepCopy A) _ _ _ (copyRun_suffix y x)]
  simp only [Function.iterate_one,Option.bind_some,finish]
  rfl

/-- The complete raw prefix entry equals the standard compiler initialization. -/
theorem init_eq (w : List Bool) : (machine A).init w = preCfg A 0 w [] [] [] none := by
  simp [Machine.init,machine,preCfg,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- Derive real complete output and runtime from an independently proved actual body run. -/
def executes (x y : List Bool) (a : ℕ)
    (hA : EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt y)) a) :
    EvalsToInTime (TM2.step (machine A).program) ((machine A).init x)
      (some ((machine A).halt (y ++ x))) (a + 3 * x.length + 2 * y.length + 6) := by
  have hRun :
      (fun c : Option (TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A)) =>
        c.bind (TM2.step (program A)))^[(x.length + 2 * y.length + 4) + hA.steps +
          (2 * x.length + 2)] (some (preCfg A 0 x [] [] [] none)) =
      some ((machine A).halt (y ++ x)) := by
    rw [Function.iterate_add_apply,prefix_run,Function.iterate_add_apply,
      iterate_lift (TM2.step A.program) (TM2.step (program A)) (embed A x.reverse)
        (step A x.reverse) _ _ _ hA.evals_in_steps,transfer]
  refine ⟨⟨(x.length + 2 * y.length + 4) + hA.steps + (2 * x.length + 2), ?_⟩, ?_⟩
  · exact (init_eq A x).symm ▸ hRun
  · have hle := hA.steps_le_m
    change (x.length + 2 * y.length + 4) + hA.steps + (2 * x.length + 2) ≤
      a + 3 * x.length + 2 * y.length + 6
    omega

/-- Mathematical bound from actual body time, input retention and output-stack growth. -/
noncomputable def timePolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  p + Polynomial.C 3 * Polynomial.X +
    Polynomial.C 2 * (Polynomial.X + Polynomial.C (programPushes A.program) * p) +
    Polynomial.C 6

/-- Real encoded-input execution satisfies the polynomial derived from actual stack growth. -/
def executes_polynomial {α : Type} (encode : α → List Bool) (f : α → List Bool)
    (p : Polynomial ℕ)
    (hA : ∀ x, EvalsToInTime (TM2.step A.program) (A.init (encode x))
      (some (A.halt (f x))) (p.eval (encode x).length)) (x : α) :
    EvalsToInTime (TM2.step (machine A).program) ((machine A).init (encode x))
      (some ((machine A).halt (f x ++ encode x)))
      ((timePolynomial A p).eval (encode x).length) := by
  have hL := Machine.output_length_le A (encode x) (f x) _ (hA x)
  rw [Nat.mul_comm] at hL
  have h := executes A (encode x) (f x) _ (hA x)
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X]
  have hb := Nat.mul_le_mul_left 2 hL
  omega

/-- Standard Mathlib certificate for the real compiler on valid encoded inputs. -/
noncomputable def computableInPolyTime {α : Type} (encode : α → List Bool) (f : α → List Bool)
    (p : Polynomial ℕ)
    (hA : ∀ x, EvalsToInTime (TM2.step A.program) (A.init (encode x))
      (some (A.halt (f x))) (p.eval (encode x).length)) :
    TM2ComputableInPolyTime encode id (fun x => f x ++ encode x) where
  tm := (machine A).toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial A p
  outputsFun := fun x => by
    change TM2OutputsInTime (machine A).toFinTM2 (List.map id (encode x))
      (some (List.map id (f x ++ encode x))) ((timePolynomial A p).eval (encode x).length)
    have h := Machine.outputsInTime (machine A) _ _ _ (executes_polynomial A encode f p hA x)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h

end QEC.Coding.BitTuring.RetainedInput
