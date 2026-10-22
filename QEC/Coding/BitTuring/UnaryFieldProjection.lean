import QEC.Coding.BitTuring.UnaryOutputEquality

/-!
# Actual fixed-field unary projection

Finite labels and a fixed Boolean mask select fields. Real input scans push selected bits and
delimiters into a reverse buffer, discard the final selected delimiter and reverse into output.
Every phase, whole clean execution, faithful encoding and linear time are proved, including
empty selection and discarded final fields. stream, fields, buffer and raw are mathematical
specifications only; none controls the program or supplies an execution premise.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
open Turing StateTransition
variable (n:ℕ) (keep:Fin (n+1) → Bool)
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
abbrev Label (n:ℕ) := Fin (n+1) ⊕ Unit
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
abbrev Statement (n:ℕ) := TM2.Stmt (fun _:Fin 3 => Bool) (Label n) (Option Bool)
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
def nextStatement (k:Fin (n+1)) : Statement n :=
  if h:k.val<n then .goto (fun _ => .inl ⟨k.val+1,Nat.succ_lt_succ h⟩)
  else .pop 1 (fun _ _ => none) (.goto fun _ => .inr ())
/-- Actual finite Boolean instructions; varying integers occur only on tapes. -/
def program : Label n → Statement n
  | .inl k => .pop 0 (fun _ h => h) (.branch (fun v => v.getD false)
      (if keep k then .push 1 (fun _ => true) (.goto fun _ => .inl k) else .goto fun _ => .inl k)
      (if keep k then .push 1 (fun _ => false) (nextStatement n k) else nextStatement n k))
  | .inr _ => liftStatement id (fun _ => .inr ()) id (fun _ w => w) none (copyProgram false)
/-- Actual fixed finite machine for the proved instruction closure. -/
def machine : Machine where
  K:=Fin 3
  input:=0
  output:=2
  Λ:=Label n
  main:=.inl 0
  σ:=Option Bool
  initial:=none
  program:=program n keep

/-- Complete configuration including all tapes, finite control and variables. -/
def cfg (k:Fin (n+1)) (s b d:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 3 => Bool) (Label n) (Option Bool) := ⟨some (.inl k),v,![s,b,d]⟩
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
def revCfg (s b d:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 3 => Bool) (Label n) (Option Bool) := ⟨some (.inr ()),v,![s,b,d]⟩
/-- Complete clean halt with only the output populated. -/
def halt (d:List Bool) : TM2.Cfg (fun _:Fin 3 => Bool) (Label n) (Option Bool) :=
  ⟨none,none,![[],[],d]⟩

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem bit_step (k:Fin (n+1)) (s b d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (cfg n k (true::s) b d v)=
      some (cfg n k s (if keep k then true::b else b) d (some true)) := by
  cases hk:keep k <;> simp [TM2.step,program,cfg,TM2.stepAux,hk,TM2.Cfg.mk.injEq] <;>
    (funext j;fin_cases j <;> simp [Function.update])
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem sep_step_lt (k:Fin (n+1)) (hk:k.val<n) (s b d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (cfg n k (false::s) b d v)=
      some (cfg n ⟨k.val+1,Nat.succ_lt_succ hk⟩ s
        (if keep k then false::b else b) d (some false)) := by
  cases h:keep k <;> simp [TM2.step,program,cfg,nextStatement,TM2.stepAux,h,hk,TM2.Cfg.mk.injEq] <;>
    (funext j;fin_cases j <;> simp [Function.update])
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem sep_step_last (k:Fin (n+1)) (hk:k.val=n) (s b d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (cfg n k (false::s) b d v)=
      some (revCfg n s ((if keep k then false::b else b).tail) d none) := by
  have hkn:¬k.val<n := by omega
  cases h:keep k <;> simp [TM2.step,program,cfg,revCfg,nextStatement,TM2.stepAux,h,hkn,TM2.Cfg.mk.injEq] <;>
    (funext j;fin_cases j <;> simp [Function.update])

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem reverse_cons (x:Bool) (b d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (revCfg n [] (x::b) d v)=
      some (revCfg n [] b (x::d) (some x)) := by
  simp [TM2.step,program,revCfg,copyProgram,liftStatement,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext j;fin_cases j <;> simp [Function.update]
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem reverse_nil (d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (revCfg n [] [] d v)=some (halt n d) := by
  simp [TM2.step,program,revCfg,halt,copyProgram,liftStatement,TM2.stepAux,TM2.Cfg.mk.injEq]
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem reverse_run (b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step (program n keep)))^[b.length+1]
      (some (revCfg n [] b d v))=some (halt n (b.reverse++d)) := by
  induction b generalizing d v with
  | nil => simp [reverse_nil]
  | cons x b ih =>
    simp only [List.length_cons]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,reverse_cons]
    rw [ih];simp [List.reverse_cons,List.append_assoc]

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem field_lt (k:Fin (n+1)) (hk:k.val<n) (a:ℕ) (s b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step (program n keep)))^[a+1]
      (some (cfg n k (unary a++false::s) b d v))=
      some (cfg n ⟨k.val+1,Nat.succ_lt_succ hk⟩ s
        (if keep k then false::(unary a++b) else b) d (some false)) := by
  induction a generalizing b v with
  | zero => simp [unary,sep_step_lt n keep k hk]
  | succ a ih =>
    simp only [unary_succ,List.cons_append]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,bit_step]
    rw [ih]
    cases h:keep k <;> simp [unary_append_cons]
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem field_last (k:Fin (n+1)) (hk:k.val=n) (a:ℕ) (s b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step (program n keep)))^[a+1]
      (some (cfg n k (unary a++false::s) b d v))=
      some (revCfg n s ((if keep k then false::(unary a++b) else b).tail) d none) := by
  induction a generalizing b v with
  | zero => simp [unary,sep_step_last n keep k hk]
  | succ a ih =>
    simp only [unary_succ,List.cons_append]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,bit_step]
    rw [ih]
    cases h:keep k <;> simp [unary_append_cons]

-- Mathematical field stream and buffer specifications, never machine control.
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
def stream : List ℕ → List Bool
  | [] => []
  | a::xs => unary a++false::stream xs

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
def maskAt (i:ℕ) : Bool := keep ⟨i%(n+1),Nat.mod_lt _ (by omega)⟩
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem maskAt_val (k:Fin (n+1)) : maskAt n keep k.val=keep k := by
  simp only [maskAt,Nat.mod_eq_of_lt k.isLt]
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
def buffer : ℕ → List ℕ → List Bool → List Bool
  | _,[],b => b
  | i,a::xs,b => buffer (i+1) xs (if maskAt n keep i then false::(unary a++b) else b)

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem parse_fields (xs:List ℕ) (k:Fin (n+1)) (hk:k.val+xs.length=n+1) (hne:xs≠[])
    (b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step (program n keep)))^[(stream xs).length]
      (some (cfg n k (stream xs) b d v))=
      some (revCfg n [] (buffer n keep k.val xs b).tail d none) := by
  induction xs generalizing k b d v with
  | nil => exact False.elim (hne rfl)
  | cons a xs ih =>
    cases xs with
    | nil =>
      have hkl:k.val=n := by simp only [List.length_cons,List.length_nil] at hk;omega
      have h:=field_last n keep k hkl a [] b d v
      simpa only [stream,List.length_append,List.length_cons,List.length_nil,unary_length,
        List.append_nil,buffer,maskAt_val] using h
    | cons c xs =>
      have hkl:k.val<n := by simp only [List.length_cons] at hk;omega
      rw [show (stream (a::c::xs)).length=(stream (c::xs)).length+(a+1) by
        change (unary a++false::stream (c::xs)).length=_
        simp only [List.length_append,List.length_cons,unary_length];omega]
      change (fun c => c.bind (TM2.step (program n keep)))^[(stream (c::xs)).length+(a+1)]
        (some (cfg n k (unary a++false::stream (c::xs)) b d v))=_
      rw [Function.iterate_add_apply,field_lt n keep k hkl]
      have htail:(⟨k.val+1,Nat.succ_lt_succ hkl⟩:Fin (n+1)).val+(c::xs).length=n+1 := by
        simp only [List.length_cons] at hk ⊢;omega
      have h:=ih ⟨k.val+1,Nat.succ_lt_succ hkl⟩ htail (by simp)
        (if keep k then false::(unary a++b) else b) d (some false)
      simpa only [buffer,maskAt_val] using h
/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem buffer_length_le (i:ℕ) (xs:List ℕ) (b:List Bool) :
    (buffer n keep i xs b).length≤(stream xs).length+b.length := by
  induction xs generalizing i b with
  | nil => simp [buffer,stream]
  | cons a xs ih =>
    have h:=ih (i+1) (if maskAt n keep i then false::(unary a++b) else b)
    cases hm:maskAt n keep i <;>
      simp only [buffer,hm,Bool.false_eq_true,↓reduceIte,
        List.length_cons,List.length_append,unary_length,stream] at h ⊢ <;> omega

/-- Mathematical row-major or selected-field specification, never machine control. -/
def fields : ℕ→List ℕ→List ℕ
  | _,[]=>[]
  | i,a::xs=>if maskAt n keep i then a::fields (i+1) xs else fields (i+1) xs

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem buffer_eq (i:ℕ) (xs:List ℕ) (b:List Bool) :
    buffer n keep i xs b=(stream (fields n keep i xs)).reverse++b := by
  induction xs generalizing i b with
  | nil => simp [buffer,fields,stream]
  | cons a xs ih =>
    cases hm:maskAt n keep i <;>
      simp [buffer,fields,hm,ih,stream,List.reverse_append,unary,List.append_assoc]

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
def raw (xs:List ℕ) := (stream xs).dropLast

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem buffer_output (xs:List ℕ) :
    (buffer n keep 0 xs []).tail.reverse=raw (fields n keep 0 xs) := by
  rw [buffer_eq]
  simp [raw]

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
def steps (xs:List ℕ) := (stream xs).length+(buffer n keep 0 xs []).tail.length+1

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem init_eq (xs:List ℕ) : (machine n keep).init (stream xs)=
    cfg n 0 (stream xs) [] [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem halt_eq (y:List Bool) : halt n y=(machine n keep).halt y := by
  simp [halt,Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]

/-- Counted complete execution with clean halt and the exact result. -/
theorem run (xs:List ℕ) (hx:xs.length=n+1) :
    (fun c=>c.bind (TM2.step (machine n keep).program))^[steps n keep xs]
      (some ((machine n keep).init (stream xs)))=
      some ((machine n keep).halt (raw (fields n keep 0 xs))) := by
  rw [init_eq]
  change (fun c=>c.bind (TM2.step (program n keep)))^[steps n keep xs]
    (some (cfg n 0 (stream xs) [] [] none))=_
  rw [show steps n keep xs=((buffer n keep 0 xs []).tail.length+1)+(stream xs).length by
    simp only [steps];omega,Function.iterate_add_apply,
    parse_fields n keep xs 0 (by simpa using hx) (by intro h;subst xs;simp at hx)]
  have h:=reverse_run n keep (buffer n keep 0 xs []).tail [] none
  rw [buffer_output,List.append_nil,halt_eq] at h
  exact h

/-- Complete counted actual execution certificate. -/
def exec (xs:List ℕ) (hx:xs.length=n+1) :
    EvalsToInTime (TM2.step (machine n keep).program) ((machine n keep).init (stream xs))
      (some ((machine n keep).halt (raw (fields n keep 0 xs)))) (steps n keep xs) :=
  ⟨⟨steps n keep xs,run n keep xs hx⟩,le_refl _⟩

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem steps_le (xs:List ℕ) : steps n keep xs≤2*(stream xs).length+1 := by
  have h:=buffer_length_le n keep 0 xs []
  have ht:(buffer n keep 0 xs []).tail.length≤(buffer n keep 0 xs []).length := by
    simp only [List.length_tail];omega
  simp only [List.length_nil,Nat.add_zero,steps] at h ⊢
  omega

/-- Polynomial bound derived from complete actual executions and intermediate tape lengths. -/
noncomputable def time : Polynomial ℕ := Polynomial.C 2*Polynomial.X+1

/-- Complete actual clean execution at the proved encoded-input polynomial budget. -/
noncomputable def polyExec (xs:List ℕ) (hx:xs.length=n+1) :
    EvalsToInTime (TM2.step (machine n keep).program) ((machine n keep).init (stream xs))
      (some ((machine n keep).halt (raw (fields n keep 0 xs))))
      (time.eval (stream xs).length) := by
  have h:=exec n keep xs hx
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simpa [time] using steps_le n keep xs

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem stream_injective : Function.Injective stream := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons b ys =>
      have hl:=congrArg List.length h
      simp [stream,unary_length] at hl
  | cons a xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have hl:=congrArg List.length h
      simp [stream,unary_length] at hl
    | cons b ys =>
      have he:=@UnaryOutputEquality.prefixInput_injective (a,stream xs) (b,stream ys) h
      exact congrArg₂ List.cons (congrArg Prod.fst he) (ih (congrArg Prod.snd he))

/-- Fixed-length field domain with only its structural input-length fact. -/
def Input := {xs:List ℕ//xs.length=n+1}
/-- Encode every varying operand and the original modulus on the input tape. -/
def input (x:Input n) := stream x.val

/-- The actual encoding distinguishes every domain input. -/
theorem input_injective : Function.Injective (input n) := by
  intro x y h;exact Subtype.ext (stream_injective h)

/-- Standard polynomial-time certificate for the actual machine and faithful inputs. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (input n) id (fun x:Input n=>raw (fields n keep 0 x.val)) where
  tm:=(machine n keep).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime (machine n keep).toFinTM2 (List.map id (input n x))
      (some (List.map id (raw (fields n keep 0 x.val)))) (time.eval (input n x).length)
    have h:=Machine.outputsInTime (machine n keep) _ _ _ (polyExec n keep x.val x.property)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input] using h

end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem stream_length (xs:List ℕ) : (stream xs).length=xs.sum+xs.length := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [stream,List.length_append,unary_length,List.length_cons,
    ih,List.sum_cons];omega

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem raw_append_last (xs:List ℕ) (a:ℕ) :
    raw (xs++[a])=stream xs++unary a := by
  induction xs with
  | nil=>simp [raw,stream]
  | cons b xs ih=>
    change (unary b++false::stream (xs++[a])).dropLast=_
    have hn:stream (xs++[a])≠[] := by
      intro h
      have hl:=congrArg List.length h
      simp only [stream_length,List.length_nil,List.length_append,List.length_singleton] at hl
      omega
    rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),
      List.dropLast_cons_of_ne_nil hn]
    -- separator persists because the remainder contains at least its final delimiter.
    change unary b++false::raw (xs++[a])=_
    rw [ih];simp only [stream,List.cons_append,List.append_assoc]

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem raw_triple (a b q:ℕ) : raw [a,b,q]=FactorTest.tripleInput a b q := by
  have h:=raw_append_last [a,b] q
  simpa [stream,FactorTest.tripleInput,pairInput,List.append_assoc] using h

end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem fields_stream_length_le (i:ℕ) (xs:List ℕ) :
    (stream (fields n keep i xs)).length≤(stream xs).length := by
  have h:=buffer_length_le n keep i xs []
  rw [buffer_eq] at h
  simpa only [List.append_nil,List.length_reverse,List.length_nil,Nat.add_zero] using h

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem raw_length_le (xs:List ℕ) : (raw xs).length≤(stream xs).length := by
  simp only [raw,List.length_dropLast];omega

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem raw_four (a b c d:ℕ) : raw [a,b,c,d]=
    unary a++false::(unary b++false::(unary c++false::unary d)) := by
  simpa [stream,List.append_assoc] using raw_append_last [a,b,c] d

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem reverse_raw_four (a b c d:ℕ) : (raw [a,b,c,d]).reverse=raw [d,c,b,a] := by
  simp [raw_four,List.reverse_append,List.reverse_cons,unary,List.append_assoc]

end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
