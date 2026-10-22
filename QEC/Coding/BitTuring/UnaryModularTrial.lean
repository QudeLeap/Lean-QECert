import QEC.Coding.BitTuring.UnaryOutputEquality
import QEC.Coding.BitTuring.UnaryModularProduct


/-!
# Actual modular product and square equality trials

One fixed Boolean machine runs the independently proved variable-modulus product program
and compares its real output with a target retained from the input. For every positive
modulus it cleanly halts with `[decide (a*b%q = r)]`. Canonical targets `r < q` identify
this flag with true ZMod product equality; duplicated operands give square equality.

Whole counted execution, faithful input and standard polynomial-time certificates are
proved from real instructions. Time is quadratic in unary encoded input length. No claim
is made for binary natural input or the complete explicit PK22 runtime. These trials are
primitives for bounded square-root and modular matrix/inverse computations. The full
searches, sparse CSS runtime and strong arithmetic spectral estimate remain unfinished.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality

/-- One fixed actual modular-product equality machine with dynamic target and modulus. -/
def machine : Machine := UnaryOutputEquality.machine ModularProduct.machine
/-- The actual quadratic full-input polynomial inherited from proved instruction execution. -/
noncomputable def time : Polynomial ℕ := timePolynomial ModularProduct.machine ModularProduct.time

/-- Faithful tape input carrying both operands, target and modulus. -/
def input (a b r q : ℕ) : List Bool := prefixInput r (FactorTest.tripleInput a b q)

/-- Actual complete clean execution decides modular product equality in polynomial time. -/
noncomputable def polyExec (a b r q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (input a b r q))
      (some (machine.halt [decide ((a*b)%q=r)])) (time.eval (input a b r q).length) :=
  executes_polynomial ModularProduct.machine r ((a*b)%q) _ ModularProduct.time
    (ModularProduct.polyExec a b q hq)

/-- Standard output certificate for the actual modular equality flag. -/
noncomputable def outputsInTime (a b r q : ℕ) (hq : 0<q) :
    TM2OutputsInTime machine.toFinTM2 (input a b r q)
      (some [decide ((a*b)%q=r)]) (time.eval (input a b r q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec a b r q hq)

/-- Canonical targets identify natural residue equality with true ZMod product equality. -/
theorem product_eq_iff (a b r q : ℕ) (hq : 0<q) (hr : r<q) :
    ((a*b)%q=r) ↔ ((a:ZMod q)*(b:ZMod q)=(r:ZMod q)) := by
  let : NeZero q := ⟨hq.ne'⟩
  constructor
  · intro h
    apply ZMod.val_injective q
    simpa only [←Nat.cast_mul,ZMod.val_natCast,Nat.mod_eq_of_lt hr] using h
  · intro h
    have hh := congrArg ZMod.val h
    simpa only [←Nat.cast_mul,ZMod.val_natCast,Nat.mod_eq_of_lt hr] using hh

/-- The actual flag decides true ZMod product equality for a canonical target. -/
noncomputable def outputsZModProductInTime (a b r q : ℕ) (hq : 0<q) (hr : r<q) :
    TM2OutputsInTime machine.toFinTM2 (input a b r q)
      (some [decide ((a:ZMod q)*(b:ZMod q)=(r:ZMod q))]) (time.eval (input a b r q).length) := by
  simpa only [product_eq_iff a b r q hq hr] using outputsInTime a b r q hq

/-- Duplicated actual operands decide true ZMod square equality for a canonical target. -/
noncomputable def outputsZModSquareInTime (a r q : ℕ) (hq : 0<q) (hr : r<q) :
    TM2OutputsInTime machine.toFinTM2 (input a a r q)
      (some [decide ((a:ZMod q)^2=(r:ZMod q))]) (time.eval (input a a r q).length) := by
  simpa only [pow_two] using outputsZModProductInTime a a r q hq hr

/-- Standard actual modular product equality certificate on faithfully encoded inputs. -/
noncomputable def productComputableInPolyTime :
    TM2ComputableInPolyTime (UnaryOutputEquality.input ModularProduct.input)
      FactorTest.boolBits
      (fun z:(ℕ×(ℕ×ℕ+))×ℕ => decide ((z.1.1*z.1.2.1)%z.1.2.2.val=z.2)) :=
  computableInPolyTime ModularProduct.machine ModularProduct.input
    (fun x => (x.1*x.2.1)%x.2.2.val) ModularProduct.time
    (fun x => ModularProduct.polyExec x.1 x.2.1 x.2.2.val x.2.2.pos)

/-- Encode a square trial body by duplicating the actual operand. -/
def squareInput (x : ℕ×ℕ+) : List Bool := FactorTest.tripleInput x.1 x.1 x.2.val

/-- Duplicated-operand positive-modulus body inputs are faithful. -/
theorem squareInput_injective : Function.Injective squareInput := by
  intro x y h
  have he := @FactorTest.tripleInput_injective (x.1,(x.1,x.2.val)) (y.1,(y.1,y.2.val)) h
  exact Prod.ext (congrArg (fun z:ℕ×(ℕ×ℕ) => z.1) he)
    (Subtype.ext (congrArg (fun z:ℕ×(ℕ×ℕ) => z.2.2) he))

/-- Standard actual modular square equality certificate on faithfully encoded inputs. -/
noncomputable def squareComputableInPolyTime :
    TM2ComputableInPolyTime (UnaryOutputEquality.input squareInput) FactorTest.boolBits
      (fun z:(ℕ×ℕ+)×ℕ => decide ((z.1.1*z.1.1)%z.1.2.val=z.2)) :=
  computableInPolyTime ModularProduct.machine squareInput
    (fun x => (x.1*x.1)%x.2.val) ModularProduct.time
    (fun x => ModularProduct.polyExec x.1 x.1 x.2.val x.2.pos)


/-- Complete actual label count for parsing, modular product, comparison and extraction. -/
def steps (a b r q : ℕ) : ℕ := ModularProduct.steps a b q+r+max ((a*b)%q) r+3

/-- The whole genuine machine run cleanly halts at the exact counted step with the correct flag. -/
theorem run (a b r q : ℕ) (hq : 0<q) :
    (fun c => c.bind (TM2.step machine.program))^[steps a b r q]
      (some (machine.init (input a b r q))) =
      some (machine.halt [decide ((a*b)%q=r)]) := by
  let h := executes ModularProduct.machine r ((a*b)%q) (FactorTest.tripleInput a b q)
    (ModularProduct.steps a b q) (ModularProduct.exec a b q hq)
  have hs : h.steps=steps a b r q := by
    change (max ((a*b)%q) r+2)+ModularProduct.steps a b q+(r+1)=
      ModularProduct.steps a b q+r+max ((a*b)%q) r+3
    omega
  rw [←hs]
  exact h.evals_in_steps

/-- The full product trial input distinguishes operands, positive modulus and target. -/
theorem productInput_injective :
    Function.Injective (UnaryOutputEquality.input ModularProduct.input) :=
  UnaryOutputEquality.input_injective ModularProduct.input ModularProduct.input_injective

/-- The full square trial input distinguishes operand, positive modulus and target. -/
theorem squareTrialInput_injective :
    Function.Injective (UnaryOutputEquality.input squareInput) :=
  UnaryOutputEquality.input_injective squareInput squareInput_injective

end QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
