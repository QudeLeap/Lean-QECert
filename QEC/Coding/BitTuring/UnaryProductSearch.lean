import QEC.Coding.BitTuring.UnaryProductTrial
import QEC.Coding.BitTuring.UnarySquareRoot

/-!
# Actual least unary modular-product solution search

A real FlagLoop executes the candidate-only product trial. Mathematical decoding and Nat.find
serve solely as proof invariants. Actual failure-before-minimum and terminal true flag give
complete clean halt, at most q calls and cubic unary-input time. Domain existence is a
mathematical fact, never supplied execution, answer or cost evidence. UnaryFieldInverse derives
this domain from genuine finite-field inverse algebra.
-/

namespace QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch
open Turing StateTransition

open SquareRoot (readNat afterNat readNat_prefix afterNat_prefix readNat_unary state_succ_after)

/-- The faithful record is exactly three delimited unary prefixes and the modulus. -/
theorem record_eq (r a b q : ℕ) : ProductAdvance.record r a b q=
    UnaryOutputEquality.prefixInput r
      (UnaryOutputEquality.prefixInput a (UnaryOutputEquality.prefixInput b (unary q))) := by rfl

/-- Semantic iteration specification; arithmetic here is never machine data or a callback. -/
def F (w : List Bool) : Bool×List Bool :=
  let r := readNat w
  let a := readNat (afterNat w)
  let b := readNat (afterNat (afterNat w))
  let q := readNat (afterNat (afterNat (afterNat w)))
  if (a*b)%q=r then (true,unary a) else (false,ProductAdvance.record r (a+1) b q)

/-- Actual faithful record decoding gives the precise product-trial semantic step. -/
theorem F_record (r a b q : ℕ) : F (ProductAdvance.record r a b q)=
    if (a*b)%q=r then (true,unary a) else (false,ProductAdvance.record r (a+1) b q) := by
  simp only [F,record_eq,readNat_prefix,afterNat_prefix,readNat_unary]

/-- The proved actual body output matches the loop semantic specification. -/
theorem result_eq (r a b q : ℕ) : ProductTrial.result r a b q=
    (F (ProductAdvance.record r a b q)).1::(F (ProductAdvance.record r a b q)).2 := by
  rw [F_record]
  by_cases h:(a*b)%q=r <;> simp [ProductTrial.result,ProductAdvance.output,h]

/-- Mathematical least-root specification from existence; it is never executed as a callback. -/
def index (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) : ℕ := Nat.find h

/-- The mathematical least root is strictly below the positive tape modulus. -/
theorem index_lt (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) : index r b q h<q :=
  (Nat.find_spec h).1

/-- The least root satisfies the actual natural residue predicate. -/
theorem index_residue (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) :
    ((index r b q h)*b)%q=r := (Nat.find_spec h).2

/-- Every earlier candidate fails the actual product equality predicate. -/
theorem before_index (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) (i : ℕ) (hi : i< index r b q h) :
    (i*b)%q≠r := by
  intro he
  exact Nat.find_min h hi ⟨hi.trans (index_lt r b q h),he⟩

/-- The entire preterminal semantic orbit is the faithful incrementing candidate record. -/
theorem state_record (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) (i : ℕ) (hi : i≤ index r b q h) :
    FlagLoop.state F i (ProductAdvance.record r 0 b q)=ProductAdvance.record r i b q := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [state_succ_after]
      rw [ih (by omega),F_record]
      simp [before_index r b q h i (by omega)]

/-- The terminal semantic payload is exactly the least unary root. -/
theorem state_final (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) :
    FlagLoop.state F (index r b q h+1) (ProductAdvance.record r 0 b q)=unary (index r b q h) := by
  rw [state_succ_after,state_record r b q h _ (le_refl _),F_record]
  simp [index_residue r b q h]


/-- Actual fixed finite machine for this proved instruction/selector closure. -/
def machine : Machine := FlagLoop.machine ProductTrial.machine

/-- Mathematical polynomial derived from the whole actual instruction execution. -/
noncomputable def time : Polynomial ℕ :=
  FlagLoop.timePolynomial ProductTrial.time Polynomial.X (Polynomial.C 3*Polynomial.X)

/-- Complete genuine instruction execution satisfies its derived input polynomial. -/
noncomputable def polyExec (r b q : ℕ) (hq : 0<q) (h : ∃ n, n<q ∧ (n*b)%q=r) :
    EvalsToInTime (TM2.step machine.program) (machine.init (ProductAdvance.record r 0 b q))
      (some (machine.halt (unary (index r b q h))))
      (time.eval (ProductAdvance.record r 0 b q).length) := by
  let L := (ProductAdvance.record r 0 b q).length
  have hj := index_lt r b q h
  have hlength : ∀ i≤ index r b q h+1,
      (FlagLoop.state F i (ProductAdvance.record r 0 b q)).length≤
        (Polynomial.C 3*Polynomial.X).eval L := by
    intro i hi
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    by_cases hil:i≤ index r b q h
    · rw [state_record r b q h i hil,ProductAdvance.record_length]
      dsimp only [L]
      rw [ProductAdvance.record_length]
      omega
    · have he:i=index r b q h+1 := by omega
      rw [he,state_final,unary_length]
      dsimp only [L]
      rw [ProductAdvance.record_length]
      omega
  have hA : ∀ i≤ index r b q h,
      EvalsToInTime (TM2.step ProductTrial.machine.program)
        (ProductTrial.machine.init (FlagLoop.state F i (ProductAdvance.record r 0 b q)))
        (some (ProductTrial.machine.halt
          ((F (FlagLoop.state F i (ProductAdvance.record r 0 b q))).1::
            (F (FlagLoop.state F i (ProductAdvance.record r 0 b q))).2)))
        (ProductTrial.time.eval (FlagLoop.state F i (ProductAdvance.record r 0 b q)).length) := by
    intro i hi
    rw [state_record r b q h i hi]
    rw [←result_eq]
    exact ProductTrial.polyExec r i b q hq
  have hn:index r b q h≤Polynomial.X.eval L := by
    simp only [Polynomial.eval_X]
    dsimp only [L]
    rw [ProductAdvance.record_length]
    omega
  have hcontinue:∀ i< index r b q h,
      (F (FlagLoop.state F i (ProductAdvance.record r 0 b q))).1=false := by
    intro i hi
    rw [state_record r b q h i (by omega),F_record]
    simp [before_index r b q h i hi]
  have hfinal:(F (FlagLoop.state F (index r b q h) (ProductAdvance.record r 0 b q))).1=true := by
    rw [state_record r b q h _ (le_refl _),F_record]
    simp [index_residue r b q h]
  have hr := FlagLoop.executes_polynomial ProductTrial.machine ProductTrial.input_ne_output
    F (index r b q h) (ProductAdvance.record r 0 b q) ProductTrial.time Polynomial.X
      (Polynomial.C 3*Polynomial.X) hA hn hlength hcontinue hfinal
  rw [state_final] at hr
  exact hr


/-- Standard Mathlib output certificate from the genuine complete machine execution. -/
noncomputable def outputsInTime (r b q : ℕ) (hq : 0<q) (h : ∃ n, n<q ∧ (n*b)%q=r) :
    TM2OutputsInTime machine.toFinTM2 (ProductAdvance.record r 0 b q)
      (some (unary (index r b q h))) (time.eval (ProductAdvance.record r 0 b q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec r b q hq h)

/-- Mathematical domain with target, fixed factor and positive modulus. -/
abbrev Domain := {z:ℕ×(ℕ×ℕ) // 0<z.2.2 ∧ ∃ n, n<z.2.2 ∧ (n*z.2.1)%z.2.2=z.1}
/-- Faithful unary input carrying every non-proof parameter. -/
def input (x : Domain) : List Bool := ProductAdvance.record x.val.1 0 x.val.2.1 x.val.2.2
/-- Counted actual tape transition or phase, preserving the complete stated configuration. -/
def root (x : Domain) : ℕ := index x.val.1 x.val.2.1 x.val.2.2 x.property.2
/-- The complete tape encoding distinguishes the target, fixed factor and modulus. -/
theorem input_injective : Function.Injective input := by
  intro x y h
  have he := ModularTrial.productInput_injective (a₁:=((0,(x.val.2.1,⟨x.val.2.2,x.property.1⟩)),x.val.1))
    (a₂:=((0,(y.val.2.1,⟨y.val.2.2,y.property.1⟩)),y.val.1)) h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.2) he)
    (Prod.ext (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.1.2.1) he)
      (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.1.2.2.val) he))
/-- Standard polynomial-time certificate using the actual machine and faithful input. -/
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary root where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun x => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary (root x)))) (time.eval (input x).length)
    have h := outputsInTime x.val.1 x.val.2.1 x.val.2.2 x.property.1 x.property.2
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,root] using h
end QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch
