import QEC.Coding.BitTuring.FixedLiteral
import QEC.Coding.BitTuring.UnaryModularNegation

/-!
# Actual q-only canonical signed coefficient emission

For a fixed original integer coefficient, actual literal instructions write its magnitude.
The negative branch really constructs magnitude/q on tapes through input retention and runs
canonical modular negation. The varying modulus is the only input. The whole clean run has
a derived linear unary-input bound and emits the exact original Int cast into ZMod.
The domain holds only positive q and the coefficient bound; input is proved faithful.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.SignedCoefficient
open Turing StateTransition
/-- Fixed signed source coefficient; varying modulus is supplied only as unary input. -/
def machine (c:ℤ) : Machine := if c<0 then
  Composition.machine (FixedLiteral.prefixMachine (unary c.natAbs++[false])) ModularNegation.machine
  else FixedLiteral.machine (unary c.natAbs)
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
def output (c:ℤ) (q:ℕ) := if c<0 then ModularNegation.output c.natAbs q else c.natAbs
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def time (c:ℤ) : Polynomial ℕ :=
  Polynomial.C 9*Polynomial.X+Polynomial.C (7*c.natAbs+20)
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def exec (c:ℤ) (q:ℕ) (hc:c.natAbs<q) :
    EvalsToInTime (TM2.step (machine c).program) ((machine c).init (unary q))
      (some ((machine c).halt (unary (output c q)))) ((time c).eval (unary q).length) := by
  by_cases hn:c<0
  · rw [machine,if_pos hn,output,if_pos hn]
    have hp:=FixedLiteral.prefixExec (unary c.natAbs++[false]) (unary q)
    rw [show (unary c.natAbs++[false])++unary q=pairInput c.natAbs q by
      simp [pairInput,List.append_assoc]] at hp
    have h:=Composition.executes (FixedLiteral.prefixMachine (unary c.natAbs++[false])) ModularNegation.machine
      _ _ _ _ _ hp (ModularNegation.polyExec c.natAbs q hc.le)
    refine {h with steps_le_m:=h.steps_le_m.trans ?_}
    simp only [time,FixedLiteral.prefixTime,ModularNegation.time,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,unary_length,pairInput_length,
      List.length_append,List.length_singleton]
    omega
  · rw [machine,if_neg hn,output,if_neg hn]
    have h:=FixedLiteral.exec (unary c.natAbs) (unary q)
    refine {h with steps_le_m:=h.steps_le_m.trans ?_}
    simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,unary_length]
    omega

/-- The emitted canonical natural is the original signed integer cast, not an assumed result. -/
theorem output_eq_val (c:ℤ) (q:ℕ) (hq:0<q) (hc:c.natAbs<q) :
    output c q=(c:ZMod q).val := by
  let : NeZero q:=⟨hq.ne'⟩
  by_cases hn:c<0
  · rw [output,if_pos hn,ModularNegation.output_eq_neg _ _ hq hc]
    have hz : c=-(c.natAbs:ℤ) := by omega
    have he:(c:ZMod q)=-(c.natAbs:ZMod q) := by
      have he' := congrArg (fun z:ℤ=>(z:ZMod q)) hz
      simpa only [Int.cast_neg,Int.cast_natCast] using he'
    rw [he]
  · rw [output,if_neg hn]
    have hz : c=(c.natAbs:ℤ) := by omega
    have he:(c:ZMod q)=(c.natAbs:ZMod q) := by
      have he' := congrArg (fun z:ℤ=>(z:ZMod q)) hz
      simpa only [Int.cast_natCast] using he'
    rw [he]
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hc]


/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def outputsInTime (c:ℤ) (q:ℕ) (hq:0<q) (hc:c.natAbs<q) :
    TM2OutputsInTime (machine c).toFinTM2 (unary q) (some (unary (c:ZMod q).val))
      ((time c).eval (unary q).length) := by
  have h:=exec c q hc
  rw [output_eq_val c q hq hc] at h
  exact Machine.outputsInTime (machine c) _ _ _ h
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
abbrev Domain (c:ℤ) := {q:ℕ+//c.natAbs<q.val}
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
def input {c:ℤ} (q:Domain c) := unary q.val.val
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
theorem input_injective (c:ℤ) : Function.Injective (@input c) := by
  intro x y h
  have he:x.val.val=y.val.val := by
    change unary x.val.val=unary y.val.val at h
    simpa only [unary_length] using (congrArg (fun s:List Bool=>s.length) h)
  exact Subtype.ext (Subtype.ext he)

/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def computableInPolyTime (c:ℤ) :
    TM2ComputableInPolyTime (@input c) unary (fun q:Domain c=>(c:ZMod q.val.val).val) where
  tm:=(machine c).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time c
  outputsFun:=fun q=>by
    change TM2OutputsInTime (machine c).toFinTM2 (List.map id (input q))
      (some (List.map id (unary (c:ZMod q.val.val).val))) ((time c).eval (input q).length)
    have h:=outputsInTime c q.val.val q.val.pos q.property
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input] using h
end QEC.Coding.BitTuring.UnaryArithmetic.SignedCoefficient
