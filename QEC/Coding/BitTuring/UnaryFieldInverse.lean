import QEC.Coding.BitTuring.UnaryProductSearch
import QEC.Coding.BitTuring.UnaryInverseInput
import Mathlib.Algebra.Field.ZMod

/-!
# Actual finite-field inverse computation

True prime-field inverse algebra supplies the product search domain, and cancellation proves
its least candidate equals the canonical ZMod inverse. Actual pair initialization followed by
the real search gives a faithfully encoded standard polynomial-time computation of every
nonzero prime-field inverse. Time is cubic in unary input, not a binary-input runtime claim.
No inverse or cost oracle executes in the machine.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.InverseSearch
open Turing StateTransition

/-- True nonzero prime-field inverse algebra supplies a product solution below q. -/
theorem exists_candidate (q b : ℕ) (hq : q.Prime) (hb : (b:ZMod q)≠0) :
    ∃ n, n<q ∧ (n*b)%q=1 := by
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  refine ⟨((b:ZMod q)⁻¹).val,ZMod.val_lt _,?_⟩
  apply (ModularTrial.product_eq_iff _ b 1 q hq.pos hq.one_lt).mpr
  simp only [ZMod.natCast_zmod_val,Nat.cast_one]
  exact inv_mul_cancel₀ hb

/-- Cancellation identifies the actual least product solution with the canonical field inverse. -/
theorem index_eq_inverse (q b : ℕ) (hq : q.Prime) (hb : (b:ZMod q)≠0) :
    ProductSearch.index 1 b q (exists_candidate q b hq hb)=((b:ZMod q)⁻¹).val := by
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have h := (ModularTrial.product_eq_iff _ b 1 q hq.pos hq.one_lt).mp
    (ProductSearch.index_residue 1 b q (exists_candidate q b hq hb))
  have he : (ProductSearch.index 1 b q (exists_candidate q b hq hb):ZMod q)=(b:ZMod q)⁻¹ := by
    have hh := congrArg (fun z:ZMod q => z*(b:ZMod q)⁻¹) h
    simpa only [mul_assoc,mul_inv_cancel₀ hb,mul_one,Nat.cast_one,one_mul] using hh
  have hh := congrArg ZMod.val he
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt
    (ProductSearch.index_lt 1 b q (exists_candidate q b hq hb))] using hh

/-- Complete actual clean execution at the derived polynomial budget. -/
noncomputable def polyExec (q b : ℕ) (hq : q.Prime) (hb : (b:ZMod q)≠0) :
    EvalsToInTime (TM2.step ProductSearch.machine.program)
      (ProductSearch.machine.init (ProductAdvance.record 1 0 b q))
      (some (ProductSearch.machine.halt (unary ((b:ZMod q)⁻¹).val)))
      (ProductSearch.time.eval (ProductAdvance.record 1 0 b q).length) := by
  have h := ProductSearch.polyExec 1 b q hq.pos (exists_candidate q b hq hb)
  rwa [index_eq_inverse q b hq hb] at h
end QEC.Coding.BitTuring.UnaryArithmetic.InverseSearch

namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse
open Turing StateTransition

/-- Actual fixed finite machine for this fully proved instruction closure. -/
def machine : Machine := Composition.machine InverseInput.machine ProductSearch.machine
/-- Polynomial bound on the actually emitted intermediate tape length. -/
noncomputable def size : Polynomial ℕ := Polynomial.X+Polynomial.C 3
/-- Whole polynomial derived from the actual instruction executions. -/
noncomputable def time : Polynomial ℕ :=
  ProductSearch.time.comp size+Polynomial.C 2*size+Polynomial.C 2*Polynomial.X+Polynomial.C 3
/-- Complete actual clean execution at the derived polynomial budget. -/
noncomputable def polyExec (q u:ℕ) (hq:q.Prime) (hu:(u:ZMod q)≠0) :
    EvalsToInTime (TM2.step machine.program) (machine.init (pairInput u q))
      (some (machine.halt (unary ((u:ZMod q)⁻¹).val))) (time.eval (pairInput u q).length) := by
  have h := Composition.executes InverseInput.machine ProductSearch.machine _ _ _ _ _
    (InverseInput.exec u q) (InverseSearch.polyExec q u hq hu)
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simp only [ProductAdvance.record_length,pairInput_length,time,size,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_comp]
  have he:1+0+u+q+3=u+q+1+3 := by omega
  rw [he];omega
/-- Standard output certificate obtained from the actual complete instruction run. -/
noncomputable def outputsInTime (q u:ℕ) (hq:q.Prime) (hu:(u:ZMod q)≠0) :
    TM2OutputsInTime machine.toFinTM2 (pairInput u q) (some (unary ((u:ZMod q)⁻¹).val))
      (time.eval (pairInput u q).length) := Machine.outputsInTime machine _ _ _ (polyExec q u hq hu)
/-- Canonical nonzero prime-field input domain, containing no execution or cost fields. -/
abbrev Domain := {z:ℕ×ℕ // z.2.Prime ∧ z.1<z.2 ∧ (z.1:ZMod z.2)≠0}
/-- Faithful unary input carrying every non-proof parameter. -/
def input (x:Domain) : List Bool := pairInput x.val.1 x.val.2
/-- Canonical true field inverse output specification; never a machine callback. -/
def inverse (x:Domain) : ℕ := ((x.val.1:ZMod x.val.2)⁻¹).val
/-- The actual input distinguishes every non-proof domain parameter. -/
theorem input_injective : Function.Injective input := by
  intro x y h
  exact Subtype.ext (pairInput_injective h)
/-- Standard polynomial-time certificate using the actual machine and faithful input. -/
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary inverse where
  tm:=machine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary (inverse x)))) (time.eval (input x).length)
    have h:=outputsInTime x.val.2 x.val.1 x.property.1 x.property.2.2
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,inverse] using h
end QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse
