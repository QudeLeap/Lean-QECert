import QEC.Coding.BitTuring.UnaryFieldInverse
import QEC.Coding.ExpanderCodes.LPSSquareRootMachine

/-!
# Actual original LPS normalization scalar computation

For fixed p the q-only machine executes the original degree-root selector, writes a genuine
delimiter, retains q, initializes the real inverse record and runs the actual field inverse
program. The output is exactly the canonical scalar used by lpsEffectiveQuaternionSL. The
whole execution yields standard unary polynomial-time and true PSL-carrier budget evidence.
Full matrix/PSL operations, sparse CSS runtime and strong arithmetic spectral growth remain
unproved; this internal closure does not realize the public PK22 main theorem.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

/-- Actual degree selection and delimiter execution retaining the original modulus. -/
def pairMachine (p:ℕ) : Machine :=
  RetainedInput.machine (Composition.machine (LPSDegreeRootMachine.machine p) UnaryDelimiter.machine)
/-- Whole polynomial for the actually executed retained root/factor pair program. -/
noncomputable def pairTime (p:ℕ) : Polynomial ℕ :=
  LPSDegreeRootMachine.time p+Polynomial.C 8*Polynomial.X+Polynomial.C 12
/-- The complete actual program emits exactly the original root and original modulus. -/
noncomputable def pairExec {p:ℕ} (a:LPSResiduePrime p) :
    EvalsToInTime (TM2.step (pairMachine p).program) ((pairMachine p).init (unary a.q))
      (some ((pairMachine p).halt (pairInput (lpsEffectiveDegreeRootIndex a) a.q)))
      ((pairTime p).eval a.q) := by
  let u := lpsEffectiveDegreeRootIndex a
  have hA:=Composition.executes (LPSDegreeRootMachine.machine p) UnaryDelimiter.machine _ _ _ _ _
    (LPSDegreeRootMachine.polyExec a) (UnaryDelimiter.exec u)
  have h:=RetainedInput.executes (Composition.machine (LPSDegreeRootMachine.machine p) UnaryDelimiter.machine)
    (unary a.q) (unary u++[false]) _ hA
  have he:(unary u++[false])++unary a.q=pairInput u a.q := by simp [pairInput,List.append_assoc]
  rw [he] at h
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simp only [List.length_append,List.length_cons,List.length_nil,unary_length,
    pairTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  have hu:=lpsEffectiveDegreeRootIndex_lt a
  dsimp only [u] at ⊢
  omega

/-- Actual fixed finite machine for this fully proved instruction closure. -/
def machine (p:ℕ) : Machine := Composition.machine (pairMachine p) ModularInverse.machine
/-- Polynomial bound on the actually emitted intermediate tape length. -/
noncomputable def size : Polynomial ℕ := Polynomial.C 2*Polynomial.X+Polynomial.C 1
/-- Whole polynomial derived from the actual instruction executions. -/
noncomputable def time (p:ℕ) : Polynomial ℕ :=
  ModularInverse.time.comp size+Polynomial.C 2*size+pairTime p+Polynomial.C 2

/-- Canonical inverse of the original degree root used for quaternion normalization. -/
def scalar {p:ℕ} (a:LPSResiduePrime p) : ℕ := (lpsEffectiveDegreeRoot a)⁻¹ |>.val

/-- The canonical returned scalar casts to the exact original field inverse. -/
theorem scalar_cast {p:ℕ} (a:LPSResiduePrime p) :
    (scalar a:ZMod a.q)=(lpsEffectiveDegreeRoot a)⁻¹ := ZMod.natCast_zmod_val _

/-- The returned scalar is exactly the one in the original normalized SL matrix. -/
theorem scalar_normalizes {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    (scalar a:ZMod a.q) • lpsQuaternionMatrix a.q t=(lpsEffectiveQuaternionSL a t ht).val := by
  rw [scalar_cast]
  rfl

/-- Complete actual clean execution at the derived polynomial budget. -/
noncomputable def polyExec {p:ℕ} (a:LPSResiduePrime p) :
    EvalsToInTime (TM2.step (machine p).program) ((machine p).init (unary a.q))
      (some ((machine p).halt (unary (scalar a)))) ((time p).eval (unary a.q).length) := by
  have hB:=ModularInverse.polyExec a.q (lpsEffectiveDegreeRootIndex a) a.prime
    (lpsEffectiveDegreeRoot_ne_zero a)
  have h:=Composition.executes (pairMachine p) ModularInverse.machine _ _ _ _ _ (pairExec a) hB
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simp only [pairInput_length,unary_length,time,size,Polynomial.eval_add,Polynomial.eval_comp,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  have hu:=lpsEffectiveDegreeRootIndex_lt a
  have hp:=Composition.polynomial_eval_monotone ModularInverse.time
    (show lpsEffectiveDegreeRootIndex a+a.q+1≤2*a.q+1 by omega)
  change ModularInverse.time.eval (lpsEffectiveDegreeRootIndex a+a.q+1)≤
    ModularInverse.time.eval (2*a.q+1) at hp
  omega
/-- Standard output certificate obtained from the actual complete instruction run. -/
noncomputable def outputsInTime {p:ℕ} (a:LPSResiduePrime p) :
    TM2OutputsInTime (machine p).toFinTM2 (unary a.q) (some (unary (scalar a)))
      ((time p).eval (unary a.q).length) := Machine.outputsInTime (machine p) _ _ _ (polyExec a)
/-- Standard polynomial-time certificate using the actual machine and faithful input. -/
noncomputable def computableInPolyTime (p:ℕ) :
    TM2ComputableInPolyTime (fun a:LPSResiduePrime p => unary a.q) unary scalar where
  tm:=(machine p).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time p
  outputsFun:=fun a => by
    change TM2OutputsInTime (machine p).toFinTM2 (List.map id (unary a.q))
      (some (List.map id (unary (scalar a)))) ((time p).eval (unary a.q).length)
    have h:=outputsInTime a
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
open scoped MatrixGroups
/-- Complete actual source execution at its true PSL-carrier polynomial budget. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) :
    EvalsToInTime (TM2.step (machine p).program) ((machine p).init (unary a.q))
      (some ((machine p).halt (unary (scalar a)))) ((time p).eval (2*Fintype.card PSL(2,ZMod a.q))) := by
  have h:=polyExec a
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  rw [unary_length]
  exact Composition.polynomial_eval_monotone (time p) a.q_le_two_mul_card_psl
/-- Standard actual output certificate at the proved PSL-carrier budget. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) :
    TM2OutputsInTime (machine p).toFinTM2 (unary a.q) (some (unary (scalar a)))
      ((time p).eval (2*Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime (machine p) _ _ _ (blockExec a)
end QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
