import QEC.Coding.BitTuring.UnarySquareRootTrial
import QEC.Coding.BitTuring.FlagLoop
import Mathlib.Data.Nat.Find

/-!
# Actual least unary square-root search

The fixed Boolean machine repeatedly executes the actual square trial and candidate update.
The semantic decode and least-root invariant are proof helpers, never machine data. Before
the least root the computed flag is false and the actual candidate advances; at the root it
is true and the genuine FlagLoop returns that candidate with all auxiliary tapes empty.

A root below the positive tape modulus gives at most q calls, each with quadratic time and
record length at most three times the initial input length. These proved facts derive a cubic
unary input polynomial and standard Mathlib computation certificate. Existence is a mathematical
domain condition, not an execution or cost field. LPSSquareRootMachine independently derives
the domain for both original LPS selectors. Boolean is only the encoding alphabet.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot
open Turing StateTransition

/-- Semantic unary-prefix length decoder used only by correctness proofs. -/
def readNat (w : List Bool) : ℕ := (w.takeWhile id).length
/-- Semantic delimiter-tail decoder used only by correctness proofs. -/
def afterNat (w : List Bool) : List Bool := (w.dropWhile id).tail

/-- The true unary prefix decoder recovers the actual natural operand. -/
theorem readNat_prefix (n : ℕ) (w : List Bool) :
    readNat (UnaryOutputEquality.prefixInput n w)=n := by
  simp [readNat,UnaryOutputEquality.prefixInput_takeWhile,unary_length]

/-- The true delimiter decoder recovers the unchanged actual payload. -/
theorem afterNat_prefix (n : ℕ) (w : List Bool) :
    afterNat (UnaryOutputEquality.prefixInput n w)=w := by
  simp [afterNat,UnaryOutputEquality.prefixInput_dropWhile]

/-- A plain unary tape decodes to its exact length. -/
theorem readNat_unary (n : ℕ) : readNat (unary n)=n := by
  simp [readNat,unary]

/-- The faithful record is exactly three delimited unary prefixes and the modulus. -/
theorem record_eq (r a q : ℕ) : SquareRootAdvance.record r a q=
    UnaryOutputEquality.prefixInput r
      (UnaryOutputEquality.prefixInput a (UnaryOutputEquality.prefixInput a (unary q))) := by rfl

/-- Semantic iteration specification; arithmetic here is never machine data or a callback. -/
def F (w : List Bool) : Bool×List Bool :=
  let r := readNat w
  let a := readNat (afterNat w)
  let q := readNat (afterNat (afterNat (afterNat w)))
  if (a*a)%q=r then (true,unary a) else (false,SquareRootAdvance.record r (a+1) q)

/-- Actual faithful record decoding gives the precise square-trial semantic step. -/
theorem F_record (r a q : ℕ) : F (SquareRootAdvance.record r a q)=
    if (a*a)%q=r then (true,unary a) else (false,SquareRootAdvance.record r (a+1) q) := by
  simp only [F,record_eq,readNat_prefix,afterNat_prefix,readNat_unary]

/-- The proved actual body output matches the loop semantic specification. -/
theorem result_eq (r a q : ℕ) : SquareRootTrial.result r a q=
    (F (SquareRootAdvance.record r a q)).1::(F (SquareRootAdvance.record r a q)).2 := by
  rw [F_record]
  by_cases h:(a*a)%q=r <;> simp [SquareRootTrial.result,SquareRootAdvance.output,h]

/-- Mathematical least-root specification from existence; it is never executed as a callback. -/
def index (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) : ℕ := Nat.find h

/-- The mathematical least root is strictly below the positive tape modulus. -/
theorem index_lt (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) : index r q h<q :=
  (Nat.find_spec h).1

/-- The least root satisfies the actual natural residue predicate. -/
theorem index_residue (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) :
    ((index r q h)*(index r q h))%q=r := (Nat.find_spec h).2

/-- Every earlier candidate fails the actual square equality predicate. -/
theorem before_index (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) (i : ℕ) (hi : i< index r q h) :
    (i*i)%q≠r := by
  intro he
  exact Nat.find_min h hi ⟨hi.trans (index_lt r q h),he⟩

/-- The next semantic state is the preceding state's specified payload. -/
theorem state_succ_after (F : List Bool → Bool×List Bool) (n : ℕ) (x : List Bool) :
    FlagLoop.state F (n+1) x=(F (FlagLoop.state F n x)).2 :=
  Function.iterate_succ_apply' _ _ _

/-- The entire preterminal semantic orbit is the faithful incrementing candidate record. -/
theorem state_record (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) (i : ℕ) (hi : i≤ index r q h) :
    FlagLoop.state F i (SquareRootAdvance.record r 0 q)=SquareRootAdvance.record r i q := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [state_succ_after]
      rw [ih (by omega),F_record]
      simp [before_index r q h i (by omega)]

/-- The terminal semantic payload is exactly the least unary root. -/
theorem state_final (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) :
    FlagLoop.state F (index r q h+1) (SquareRootAdvance.record r 0 q)=unary (index r q h) := by
  rw [state_succ_after,state_record r q h _ (le_refl _),F_record]
  simp [index_residue r q h]


/-- Actual fixed finite machine for this proved instruction/selector closure. -/
def machine : Machine := FlagLoop.machine SquareRootTrial.machine

/-- Mathematical polynomial derived from the whole actual instruction execution. -/
noncomputable def time : Polynomial ℕ :=
  FlagLoop.timePolynomial SquareRootTrial.time Polynomial.X (Polynomial.C 3*Polynomial.X)

/-- Complete genuine instruction execution satisfies its derived input polynomial. -/
noncomputable def polyExec (r q : ℕ) (hq : 0<q) (h : ∃ n, n<q ∧ (n*n)%q=r) :
    EvalsToInTime (TM2.step machine.program) (machine.init (SquareRootAdvance.record r 0 q))
      (some (machine.halt (unary (index r q h))))
      (time.eval (SquareRootAdvance.record r 0 q).length) := by
  let L := (SquareRootAdvance.record r 0 q).length
  have hj := index_lt r q h
  have hlength : ∀ i≤ index r q h+1,
      (FlagLoop.state F i (SquareRootAdvance.record r 0 q)).length≤
        (Polynomial.C 3*Polynomial.X).eval L := by
    intro i hi
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    by_cases hil:i≤ index r q h
    · rw [state_record r q h i hil,SquareRootAdvance.record_length]
      dsimp only [L]
      rw [SquareRootAdvance.record_length]
      omega
    · have he:i=index r q h+1 := by omega
      rw [he,state_final,unary_length]
      dsimp only [L]
      rw [SquareRootAdvance.record_length]
      omega
  have hA : ∀ i≤ index r q h,
      EvalsToInTime (TM2.step SquareRootTrial.machine.program)
        (SquareRootTrial.machine.init (FlagLoop.state F i (SquareRootAdvance.record r 0 q)))
        (some (SquareRootTrial.machine.halt
          ((F (FlagLoop.state F i (SquareRootAdvance.record r 0 q))).1::
            (F (FlagLoop.state F i (SquareRootAdvance.record r 0 q))).2)))
        (SquareRootTrial.time.eval (FlagLoop.state F i (SquareRootAdvance.record r 0 q)).length) := by
    intro i hi
    rw [state_record r q h i hi]
    rw [←result_eq]
    exact SquareRootTrial.polyExec r i q hq
  have hn:index r q h≤Polynomial.X.eval L := by
    simp only [Polynomial.eval_X]
    dsimp only [L]
    rw [SquareRootAdvance.record_length]
    omega
  have hcontinue:∀ i< index r q h,
      (F (FlagLoop.state F i (SquareRootAdvance.record r 0 q))).1=false := by
    intro i hi
    rw [state_record r q h i (by omega),F_record]
    simp [before_index r q h i hi]
  have hfinal:(F (FlagLoop.state F (index r q h) (SquareRootAdvance.record r 0 q))).1=true := by
    rw [state_record r q h _ (le_refl _),F_record]
    simp [index_residue r q h]
  have hr := FlagLoop.executes_polynomial SquareRootTrial.machine SquareRootTrial.input_ne_output
    F (index r q h) (SquareRootAdvance.record r 0 q) SquareRootTrial.time Polynomial.X
      (Polynomial.C 3*Polynomial.X) hA hn hlength hcontinue hfinal
  rw [state_final] at hr
  exact hr


/-- Standard Mathlib output certificate from the genuine complete machine execution. -/
noncomputable def outputsInTime (r q : ℕ) (hq : 0<q) (h : ∃ n, n<q ∧ (n*n)%q=r) :
    TM2OutputsInTime machine.toFinTM2 (SquareRootAdvance.record r 0 q)
      (some (unary (index r q h))) (time.eval (SquareRootAdvance.record r 0 q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec r q hq h)

/-- Positive-modulus inputs with a mathematical root below q, not supplied execution/cost. -/
abbrev Domain := {z:ℕ×ℕ // 0<z.2 ∧ ∃ n, n<z.2 ∧ (n*n)%z.2=z.1}

/-- Faithful initial candidate-zero tape encoding for the root domain. -/
def input (x : Domain) : List Bool := SquareRootAdvance.record x.val.1 0 x.val.2

/-- Least-root output specification for the positive-root domain. -/
def root (x : Domain) : ℕ := index x.val.1 x.val.2 x.property.2

/-- The actual input encoding distinguishes every target and modulus. -/
theorem input_injective : Function.Injective input := by
  intro x y h
  have he := ModularTrial.productInput_injective (a₁:=((0,(0,⟨x.val.2,x.property.1⟩)),x.val.1))
    (a₂:=((0,(0,⟨y.val.2,y.property.1⟩)),y.val.1)) h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.2) he)
    (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.1.2.2.val) he)

/-- Standard polynomial-time computation using this actual fixed machine and faithful input. -/
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary root where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun x => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary (root x)))) (time.eval (input x).length)
    have h := outputsInTime x.val.1 x.val.2 x.property.1 x.property.2
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,root] using h

end QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot
