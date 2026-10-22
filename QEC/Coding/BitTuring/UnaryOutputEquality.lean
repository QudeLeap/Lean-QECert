import QEC.Coding.BitTuring.UnaryFactorTest

/-!
# Actual comparison of a unary machine output with a tape target

The compiler parses `unary r ++ false :: x`, retains `r` on a separate tape and runs the
actual body instructions on `x`. A clean unary body halt enters the real comparison loop;
an extraction instruction discards the order bit and cleanly halts with `[decide (n = r)]`.
The controls depend only on the fixed body machine, including when its input and output
stacks coincide. No arithmetic, equality or time callback is executed.

Every lifted instruction, tape update, handoff and counted phase is proved. A genuine
body execution in at most `m` steps yields a whole execution within `m+r+max n r+3`.
The polynomial certificate uses the actual output-length bound and full input length;
the body execution is independently proved by each consumer. UnaryModularTrial supplies
actual modular product and square instances. Boolean is only the encoding alphabet.
-/

namespace QEC.Coding.BitTuring.UnaryOutputEquality
open Turing StateTransition UnaryArithmetic
variable (A : Machine)
/-- Body tapes, a retained unary target and a fresh Boolean output tape. -/
abbrev Stack := A.K ⊕ Fin 2
/-- Body labels and six finite labels for parsing, comparison and flag extraction. -/
abbrev Label := A.Λ ⊕ (Unit ⊕ (Fin 4 ⊕ Unit))
/-- Original finite body variables and one optional comparison bit. -/
abbrev Var := A.σ × Option Bool

/-- The actual target parser entry label. -/
def mainLabel : Label A := .inr (.inl ())
/-- Embed each concrete comparison label in the combined finite control. -/
def cmpLabel (l : Fin 4) : Label A := .inr (.inr (.inl l))
/-- The actual equality-bit extraction and clean halt label. -/
def endLabel : Label A := .inr (.inr (.inr ()))
/-- Route target, actual body output and fresh comparison output tapes. -/
def cmpStack (k : Fin 3) : Stack A :=
  if k=0 then .inr 0 else if k=1 then .inl A.output else .inr 1

/-- Actual target parser, lifted body/comparison instructions and flag extraction. -/
def program : Label A → TM2.Stmt (fun _ : Stack A => Bool) (Label A) (Var A)
  | .inl l => liftStatement Sum.inl Sum.inl Prod.fst (fun v w => (w,v.2))
      (some (cmpLabel A 1)) (A.program l)
  | .inr (.inl _) => .pop (.inl A.input) (fun v h => (v.1,h))
      (.branch (fun v => v.2.getD false)
        (.push (.inr 0) (fun _ => true) (.goto fun _ => mainLabel A))
        (.load (fun _ => (A.initial,none)) (.goto fun _ => .inl A.main)))
  | .inr (.inr (.inl l)) => liftStatement (cmpStack A) (cmpLabel A) Prod.snd
      (fun v h => (v.1,h)) (some (endLabel A)) (comparisonProgram l)
  | .inr (.inr (.inr _)) => .pop (.inr 1) (fun v _ => (v.1,none))
      (.pop (.inr 1) (fun v h => (v.1,h))
        (.push (.inr 1) (fun v => v.2.getD false) (.load (fun _ => (A.initial,none)) .halt)))

/-- One fixed compiler machine, independent of the dynamic input and target. -/
def machine : Machine where
  K := Stack A
  input := .inl A.input
  output := .inr 1
  Λ := Label A
  main := mainLabel A
  σ := Var A
  initial := (A.initial,none)
  program := program A

/-- Embed body tapes while retaining the separate target and empty final output. -/
def tapes (r : List Bool) (S : A.K → List Bool) : Stack A → List Bool
  | .inl k => S k
  | .inr k => if k=0 then r else []
/-- Embed body configurations and redirect their actual halt to comparison. -/
def embed (r : List Bool) : A.Cfg → TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  liftCfg Sum.inl (fun v => (v,none)) (tapes A r) (some (cmpLabel A 1))

/-- Body tape writes commute with the target-preserving embedding. -/
theorem tapes_update (r : List Bool) (S : A.K → List Bool) (k : A.K) (w : List Bool) :
    Function.update (tapes A r S) (.inl k) w=tapes A r (Function.update S k w) := by
  funext j
  cases j with
  | inl j => by_cases h:j=k <;> simp [tapes,h]
  | inr j => simp [tapes]

/-- Every lifted body instruction has its genuine original semantics. -/
theorem stepAux (r : List Bool) (l : A.Λ) (v : A.σ) (S : A.K → List Bool) :
    TM2.stepAux (program A (.inl l)) (v,none) (tapes A r S)=
      embed A r (TM2.stepAux (A.program l) v S) :=
  stepAux_liftStatement (K:=A.K) (K':=Stack A) (Λ:=A.Λ) (Λ':=Label A)
    (σ:=A.σ) (σ':=Var A) Sum.inl Sum.inl Prod.fst (fun v w => (w,v.2))
    (some (cmpLabel A 1)) (fun v => (v,none)) (tapes A r)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (tapes_update A r) (A.program l) v S

/-- Successful actual body steps lift to successful compiled-machine steps. -/
theorem step (r : List Bool) (c c' : A.Cfg) (h : TM2.step A.program c=some c') :
    TM2.step (program A) (embed A r c)=some (embed A r c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (A.program l) v S=c' := Option.some.inj h
      rw [←hh]
      exact congrArg some (stepAux A r l v S)

/-- Full actual target parser configuration with the body payload still on input. -/
def prefixCfg (s r : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  ⟨some (mainLabel A),(A.initial,v),tapes A r (Function.update (fun _ => []) A.input s)⟩

/-- Transfer one unary target bit onto its independent tape. -/
theorem prefix_cons (s r : List Bool) (v : Option Bool) :
    TM2.step (program A) (prefixCfg A (true::s) r v)=
      some (prefixCfg A s (true::r) (some true)) := by
  simp [TM2.step,program,prefixCfg,mainLabel,TM2.stepAux,tapes,Function.update,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => by_cases h:k=A.input <;> simp [tapes,Function.update,h]
  | inr k => fin_cases k <;> simp [tapes,Function.update]

/-- Consume the delimiter, reset variables and enter the actual body. -/
theorem prefix_sep (s r : List Bool) (v : Option Bool) :
    TM2.step (program A) (prefixCfg A (false::s) r v)=some (embed A r (A.init s)) := by
  simp [TM2.step,program,prefixCfg,mainLabel,embed,liftCfg,Machine.init,
    TM2.stepAux,tapes,Function.update,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => by_cases h:k=A.input <;> simp [tapes,Function.update,h]
  | inr k => simp [tapes,Function.update]

variable {A} in
/-- Faithful unary target followed by a delimiter and the unchanged encoded body input. -/
def prefixInput (r : ℕ) (x : List Bool) : List Bool := unary r++false::x

/-- The complete actual parser executes in target plus one steps. -/
theorem prefix_run (r : ℕ) (x s : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step (program A)))^[r+1]
      (some (prefixCfg A (prefixInput r x) s v))=
      some (embed A (unary r++s) (A.init x)) := by
  induction r generalizing s v with
  | zero => simp [prefixInput,prefix_sep]
  | succ r ih =>
      simp only [prefixInput,unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,prefix_cons]
      simpa only [prefixInput,unary_append_cons,unary_succ,List.cons_append] using ih (true::s) (some true)

/-- Embed comparison tapes with all unused body tapes empty. -/
def cmpTapes (S : Fin 3 → List Bool) : Stack A → List Bool
  | .inl k => if k=A.output then S 1 else []
  | .inr k => if k=0 then S 0 else S 2

/-- Embed actual comparison configurations and redirect their halt to extraction. -/
def embedCmp : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) →
    TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  liftCfg (cmpLabel A) (fun v => (A.initial,v)) (cmpTapes A) (some (endLabel A))

/-- Comparison routing reads the exact original operand or output tape. -/
theorem cmpTapes_read (S : Fin 3 → List Bool) (k : Fin 3) :
    cmpTapes A S (cmpStack A k)=S k := by fin_cases k <;> simp [cmpTapes,cmpStack]

/-- Actual comparison writes commute with the complete tape embedding. -/
theorem cmpTapes_update (S : Fin 3 → List Bool) (k : Fin 3) (w : List Bool) :
    Function.update (cmpTapes A S) (cmpStack A k) w=cmpTapes A (Function.update S k w) := by
  funext j
  cases j with
  | inl j =>
      by_cases h:j=A.output
      · subst j
        fin_cases k <;> simp [cmpTapes,cmpStack,Function.update]
      · fin_cases k <;> simp [cmpTapes,cmpStack,Function.update,h]
  | inr j => fin_cases k <;> fin_cases j <;> simp [cmpTapes,cmpStack,Function.update]

/-- Each lifted comparison instruction has the original concrete semantics. -/
theorem stepAuxCmp (l : Fin 4) (v : Option Bool) (S : Fin 3 → List Bool) :
    TM2.stepAux (program A (cmpLabel A l)) (A.initial,v) (cmpTapes A S)=
      embedCmp A (TM2.stepAux (comparisonProgram l) v S) :=
  stepAux_liftStatement (K:=Fin 3) (K':=Stack A) (Λ:=Fin 4) (Λ':=Label A)
    (σ:=Option Bool) (σ':=Var A) (cmpStack A) (cmpLabel A) Prod.snd (fun v h => (v.1,h))
    (some (endLabel A)) (fun v => (A.initial,v)) (cmpTapes A)
    (fun _ => rfl) (fun _ _ => rfl) (cmpTapes_read A) (cmpTapes_update A) (comparisonProgram l) v S

/-- Successful actual comparison steps lift to compiled-machine steps. -/
theorem stepCmp (c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool))
    (h : TM2.step comparisonProgram c=some c') :
    TM2.step (program A) (embedCmp A c)=some (embedCmp A c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (comparisonProgram l) v S=c' := Option.some.inj h
      rw [←hh]
      exact congrArg some (stepAuxCmp A l v S)

/-- The actual clean unary body halt is exactly the comparison entry configuration. -/
theorem handoff (r n : ℕ) : embed A (unary r) (A.halt (unary n))=
    embedCmp A (comparisonCfg 1 (unary r) (unary n) [] none) := by
  simp [embed,embedCmp,liftCfg,Machine.halt,comparisonCfg,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => by_cases h:k=A.output <;> simp [tapes,cmpTapes,Function.update,h]
  | inr k => fin_cases k <;> simp [tapes,cmpTapes]

/-- Execute the genuine counted unary comparison from the two actual operands. -/
theorem run_cmp (n r : ℕ) :
    (fun c => c.bind (TM2.step (program A)))^[max n r+1]
      (some (embedCmp A (comparisonCfg 1 (unary r) (unary n) [] none)))=
      some (embedCmp A (comparisonHalt (comparisonBits n r))) :=
  iterate_lift (TM2.step comparisonProgram) (TM2.step (program A)) (embedCmp A)
    (stepCmp A) _ _ _ (FactorTest.matching_run n r)

/-- Discard the order flag and cleanly halt with the equality flag alone. -/
theorem footer (le eq : Bool) :
    TM2.step (program A) (embedCmp A (comparisonHalt [le,eq]))=
      some ((machine A).halt [eq]) := by
  simp [TM2.step,program,embedCmp,liftCfg,comparisonHalt,endLabel,Machine.halt,machine,
    TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => simp [cmpTapes,Function.update]
  | inr k => fin_cases k <;> simp [cmpTapes,Function.update]

/-- Standard initialization is exactly the full target parser configuration. -/
theorem init_eq (r : ℕ) (x : List Bool) :
    (machine A).init (prefixInput r x)=prefixCfg A (prefixInput r x) [] none := by
  simp [Machine.init,machine,prefixCfg,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => by_cases h:k=A.input <;> simp [tapes,Function.update,h]
  | inr k => fin_cases k <;> simp [tapes,Function.update]

/-- Construct a complete actual comparison run from an independently proved body run. -/
def executes (r n : ℕ) (x : List Bool) (m : ℕ)
    (hA : EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt (unary n))) m) :
    EvalsToInTime (TM2.step (machine A).program) ((machine A).init (prefixInput r x))
      (some ((machine A).halt [decide (n=r)])) (m+r+max n r+3) := by
  have hRun : (fun c => c.bind (TM2.step (program A)))^[(max n r+2)+hA.steps+(r+1)]
      (some (prefixCfg A (prefixInput r x) [] none))=
      some ((machine A).halt [decide (n=r)]) := by
    rw [Function.iterate_add_apply,prefix_run]
    simp only [List.append_nil]
    rw [Function.iterate_add_apply,
      iterate_lift (TM2.step A.program) (TM2.step (program A)) (embed A (unary r))
        (step A (unary r)) _ _ _ hA.evals_in_steps,handoff]
    rw [show max n r+2=1+(max n r+1) by omega,Function.iterate_add_apply,run_cmp]
    simp only [Function.iterate_one,Option.bind_some,comparisonBits,footer]
    rfl
  refine ⟨⟨(max n r+2)+hA.steps+(r+1),?_⟩,?_⟩
  · exact (init_eq A r x).symm ▸ hRun
  · have h := hA.steps_le_m
    change (max n r+2)+hA.steps+(r+1)≤m+r+max n r+3
    omega

/-- Exact full encoded-input length includes the target and separator. -/
theorem prefixInput_length (r : ℕ) (x : List Bool) :
    (prefixInput r x).length=r+x.length+1 := by simp [prefixInput,unary];omega

/-- Full-input polynomial derived from the fixed program push count and body polynomial. -/
noncomputable def timePolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (programPushes A.program+1)*p+Polynomial.C 3*(Polynomial.X+1)

/-- Actual output length and polynomial monotonicity bound the whole compiled run. -/
def executes_polynomial (r n : ℕ) (x : List Bool) (p : Polynomial ℕ)
    (hA : EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt (unary n))) (p.eval x.length)) :
    EvalsToInTime (TM2.step (machine A).program) ((machine A).init (prefixInput r x))
      (some ((machine A).halt [decide (n=r)]))
      ((timePolynomial A p).eval (prefixInput r x).length) := by
  let L := (prefixInput r x).length
  have hx : x.length≤L := by dsimp [L];rw [prefixInput_length];omega
  have hr : r≤L := by dsimp [L];rw [prefixInput_length];omega
  have hp := Composition.polynomial_eval_monotone p hx
  have hn := Machine.output_length_le A x (unary n) _ hA
  rw [unary_length,Nat.mul_comm] at hn
  have hc := Nat.mul_le_mul_left (programPushes A.program) hp
  have hn' : n≤L+programPushes A.program*p.eval L := hn.trans (Nat.add_le_add hx hc)
  have hmax : max n r≤n+r := max_le (by omega) (by omega)
  have h := executes A r n x _ hA
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  change p.eval x.length+r+max n r+3≤(timePolynomial A p).eval L
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,Nat.add_mul,Nat.one_mul]
  dsimp only [L] at hp hn' hmax hr ⊢
  omega

/-- Recover the exact unary target from the faithful prefix input. -/
theorem prefixInput_takeWhile (r : ℕ) (x : List Bool) :
    (prefixInput r x).takeWhile id=unary r := by
  induction r with
  | zero => simp [prefixInput,unary]
  | succ r ih => simpa [prefixInput,unary_succ] using congrArg (List.cons true) ih

/-- Recover the unchanged payload after the actual target delimiter. -/
theorem prefixInput_dropWhile (r : ℕ) (x : List Bool) :
    (prefixInput r x).dropWhile id=false::x := by
  induction r with
  | zero => simp [prefixInput,unary]
  | succ r ih => simpa [prefixInput,unary_succ] using ih

/-- The prefix input distinguishes every natural target and encoded payload. -/
theorem prefixInput_injective :
    Function.Injective (fun z:ℕ×List Bool => prefixInput z.1 z.2) := by
  intro x y h
  have hr : unary x.1=unary y.1 := by
    simpa only [prefixInput_takeWhile] using congrArg (List.takeWhile id) h
  have hx : false::x.2=false::y.2 := by
    simpa only [prefixInput_dropWhile] using congrArg (List.dropWhile id) h
  exact Prod.ext (unary_injective hr) (List.cons.inj hx).2

variable {A} in
/-- Compose the faithful prefix with a body encoding on a product domain. -/
def input {α : Type} (encode : α→List Bool) (x : α×ℕ) := prefixInput x.2 (encode x.1)

/-- A faithful body encoding gives a faithful whole equality-trial input. -/
theorem input_injective {α : Type} (encode : α→List Bool) (hi : Function.Injective encode) :
    Function.Injective (input encode) := by
  intro x y h
  have he := @prefixInput_injective (x.2,encode x.1) (y.2,encode y.1) h
  exact Prod.ext (hi (congrArg (fun z:ℕ×List Bool => z.2) he))
    (congrArg (fun z:ℕ×List Bool => z.1) he)

/-- Standard polynomial-time compiler certificate derived from genuine body runs. -/
noncomputable def computableInPolyTime {α : Type} (encode : α→List Bool) (f : α→ℕ)
    (p : Polynomial ℕ)
    (hA : ∀ x, EvalsToInTime (TM2.step A.program) (A.init (encode x))
      (some (A.halt (unary (f x)))) (p.eval (encode x).length)) :
    TM2ComputableInPolyTime (input encode) FactorTest.boolBits
      (fun z:α×ℕ => decide (f z.1=z.2)) where
  tm := (machine A).toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial A p
  outputsFun := fun z => by
    change TM2OutputsInTime (machine A).toFinTM2 (List.map id (input encode z))
      (some (List.map id (FactorTest.boolBits (decide (f z.1=z.2)))))
      ((timePolynomial A p).eval (input encode z).length)
    have h := Machine.outputsInTime (machine A) _ _ _
      (executes_polynomial A z.2 (f z.1) (encode z.1) p (hA z.1))
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,FactorTest.boolBits] using h
end QEC.Coding.BitTuring.UnaryOutputEquality
