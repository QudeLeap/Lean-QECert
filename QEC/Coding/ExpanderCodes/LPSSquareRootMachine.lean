import QEC.Coding.BitTuring.UnarySquareRoot
import QEC.Coding.BitTuring.UnarySquareRootInput
import QEC.Coding.ExpanderCodes.LPSEffectiveNormalization
import QEC.Coding.ExpanderCodes.LPSEffectivePrime

/-!
# Actual original LPS degree and residue-coordinate selectors

The complete fixed-p degree program on unary q actually writes the square-trial input,
executes the genuine bounded loop and returns the original lpsEffectiveDegreeRootIndex.
Legendre and leastness supply erased mathematical evidence, never machine answers or costs.
The source residue prime gives p<q, so the fixed literal p target is canonical.

For q=1 modulo 4, the complete residue program actually writes q-1 while retaining q, then
executes that same real loop. The first original lexicographic residue-pair solution has x=0;
its y is exactly this smallest minus-one root. Thus the returned index preserves the original
source coordinates and generator labels. Both standard unary input polynomials and carrier
budgets derive from actual execution and the proved q<=2*card(PSL) bound.

This supplies two actual selector primitives. Matrix/PSL operations, full sparse CSS runtime
and the strong arithmetic spectral estimate remain unfinished under the exact PK22 theorem.
No code-field restriction or public theorem realization is introduced.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
variable {p : ℕ}

/-- All non-q residue-prime data are proofs, so unary q faithfully identifies the source parameter. -/
theorem lpsResiduePrime_unary_injective (p : ℕ) :
    Function.Injective (fun a:LPSResiduePrime p => unary a.q) := by
  intro a b h
  have hq := unary_injective h
  cases a
  cases b
  dsimp only at hq
  cases hq
  rfl

/-- The source large-prime condition makes the fixed p target canonical. -/
theorem lpsDegree_target_lt (a : LPSResiduePrime p) : p<a.q := by
  have := a.large
  omega

/-- Actual source Legendre/root algebra supplies the numerical search domain. -/
theorem lpsDegree_numericRoot_exists (a : LPSResiduePrime p) :
    ∃ n, n<a.q ∧ (n*n)%a.q=p := by
  obtain ⟨n,hn,hs⟩ := exists_lpsDegreeRootCandidate a
  refine ⟨n,hn,?_⟩
  apply (ModularTrial.product_eq_iff n n p a.q a.prime.pos (lpsDegree_target_lt a)).mpr
  simpa only [pow_two] using hs

/-- Least numerical root is exactly the original source degree Nat.find selector. -/
theorem lpsDegree_numericRoot_index (a : LPSResiduePrime p) :
    SquareRoot.index p a.q (lpsDegree_numericRoot_exists a)=lpsEffectiveDegreeRootIndex a := by
  unfold SquareRoot.index lpsEffectiveDegreeRootIndex
  apply Nat.find_congr'
  intro n
  constructor
  · intro ⟨hn,hs⟩
    refine ⟨hn,?_⟩
    simpa only [pow_two] using
      (ModularTrial.product_eq_iff n n p a.q a.prime.pos (lpsDegree_target_lt a)).mp hs
  · intro ⟨hn,hs⟩
    refine ⟨hn,?_⟩
    apply (ModularTrial.product_eq_iff n n p a.q a.prime.pos (lpsDegree_target_lt a)).mpr
    simpa only [pow_two] using hs

end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct.LPSDegreeRootMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct
open Turing StateTransition

/-- Actual fixed finite machine for this proved instruction/selector closure. -/
def machine (p : ℕ) : Machine := Composition.machine (SquareRootInput.machine p) SquareRoot.machine

/-- Mathematical bound on the actually emitted root-search input length. -/
noncomputable def size (p : ℕ) : Polynomial ℕ := Polynomial.X+Polynomial.C (p+3)
/-- Mathematical polynomial derived from the whole actual instruction execution. -/
noncomputable def time (p : ℕ) : Polynomial ℕ :=
  SquareRoot.time.comp (size p)+Polynomial.C 2*size p+Polynomial.X+Polynomial.C 3

/-- Complete genuine instruction execution satisfies its derived input polynomial. -/
noncomputable def polyExec {p : ℕ} (a : LPSResiduePrime p) :
    EvalsToInTime (TM2.step (machine p).program) ((machine p).init (unary a.q))
      (some ((machine p).halt (unary (lpsEffectiveDegreeRootIndex a))))
      ((time p).eval (unary a.q).length) := by
  have hB := SquareRoot.polyExec p a.q a.prime.pos (lpsDegree_numericRoot_exists a)
  rw [lpsDegree_numericRoot_index] at hB
  have h := Composition.executes (SquareRootInput.machine p) SquareRoot.machine
    _ _ _ _ _ (SquareRootInput.exec p a.q) hB
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simp only [SquareRootAdvance.record_length,unary_length,time,size,Polynomial.eval_add,
    Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  have he : p+2*0+a.q+3=a.q+(p+3) := by omega
  rw [he]
  omega

/-- Standard Mathlib output certificate from the genuine complete machine execution. -/
noncomputable def outputsInTime {p : ℕ} (a : LPSResiduePrime p) :
    TM2OutputsInTime (machine p).toFinTM2 (unary a.q)
      (some (unary (lpsEffectiveDegreeRootIndex a))) ((time p).eval (unary a.q).length) :=
  Machine.outputsInTime (machine p) _ _ _ (polyExec a)

/-- Standard polynomial-time computation using this actual fixed machine and faithful input. -/
noncomputable def computableInPolyTime (p : ℕ) :
    TM2ComputableInPolyTime (fun a:LPSResiduePrime p => unary a.q) unary lpsEffectiveDegreeRootIndex where
  tm := (machine p).toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time p
  outputsFun := fun a => by
    change TM2OutputsInTime (machine p).toFinTM2 (List.map id (unary a.q))
      (some (List.map id (unary (lpsEffectiveDegreeRootIndex a)))) ((time p).eval (unary a.q).length)
    have h := outputsInTime a
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h

open scoped MatrixGroups
/-- Actual complete selector execution fits the derived polynomial in the true PSL carrier size. -/
noncomputable def blockExec {p : ℕ} (a : LPSResiduePrime p) :
    EvalsToInTime (TM2.step (machine p).program) ((machine p).init (unary a.q))
      (some ((machine p).halt (unary (lpsEffectiveDegreeRootIndex a))))
      ((time p).eval (2*Fintype.card PSL(2,ZMod a.q))) := by
  have h := polyExec a
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  rw [unary_length]
  exact Composition.polynomial_eval_monotone (time p) a.q_le_two_mul_card_psl

/-- Standard actual selector output certificate at the proved PSL carrier budget. -/
noncomputable def blockOutputsInTime {p : ℕ} (a : LPSResiduePrime p) :
    TM2OutputsInTime (machine p).toFinTM2 (unary a.q) (some (unary (lpsEffectiveDegreeRootIndex a)))
      ((time p).eval (2*Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime (machine p) _ _ _ (blockExec a)

end QEC.Coding.TannerLiftedProduct.LPSDegreeRootMachine

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
variable {p : ℕ}

/-- Canonical q-1 is the true negative-one ZMod element. -/
theorem lpsMinusRoot_natCast (a : LPSResiduePrime p) :
    ((a.q-1:ℕ):ZMod a.q)=(-1:ZMod a.q) := by
  let : NeZero a.q := ⟨a.prime.ne_zero⟩
  rw [Nat.cast_sub (by have := a.prime.pos;omega)]
  simp

/-- Source q modulo four gives a true negative-one root and numerical domain. -/
theorem lpsMinusRoot_numeric_exists (a : LPSResiduePrime p) :
    ∃ n, n<a.q ∧ (n*n)%a.q=a.q-1 := by
  let : NeZero a.q := ⟨a.prime.ne_zero⟩
  have hsq : IsSquare (-1:ZMod a.q) :=
    ZMod.exists_sq_eq_neg_one_iff.mpr (by have := a.modFour;omega)
  obtain ⟨t,ht⟩ := hsq
  refine ⟨t.val,ZMod.val_lt t,?_⟩
  apply (ModularTrial.product_eq_iff t.val t.val (a.q-1) a.q a.prime.pos (by have := a.prime.pos;omega)).mpr
  rw [ZMod.natCast_zmod_val,lpsMinusRoot_natCast]
  exact ht.symm


/-- Least negative-one root is exactly the original lexicographic residue-pair selector. -/
theorem lpsMinusRoot_pair_index (a : LPSResiduePrime p) :
    SquareRoot.index (a.q-1) a.q (lpsMinusRoot_numeric_exists a)=
      lpsEffectiveResiduePairIndex a.q := by
  let : NeZero a.q := ⟨a.prime.ne_zero⟩
  let j := SquareRoot.index (a.q-1) a.q (lpsMinusRoot_numeric_exists a)
  have hj := SquareRoot.index_lt (a.q-1) a.q (lpsMinusRoot_numeric_exists a)
  have hjsq : (j:ZMod a.q)^2=(-1:ZMod a.q) := by
    rw [←lpsMinusRoot_natCast a]
    have hmod := SquareRoot.index_residue (a.q-1) a.q (lpsMinusRoot_numeric_exists a)
    simpa only [pow_two] using
      (ModularTrial.product_eq_iff j j (a.q-1) a.q a.prime.pos
        (by have := a.prime.pos;omega)).mp hmod
  have hjCandidate : lpsResiduePairCandidate a.q j := by
    refine ⟨?_,?_⟩
    · have := a.prime.two_le
      dsimp only [j]
      nlinarith
    · rw [Nat.div_eq_of_lt hj,Nat.mod_eq_of_lt hj]
      simp only [Nat.cast_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add]
      change (j:ZMod a.q)^2+1=0
      simp [hjsq]
  have hpj : lpsEffectiveResiduePairIndex a.q≤j := Nat.find_min' (exists_lpsResiduePairCandidate a.q) hjCandidate
  have hpLt : lpsEffectiveResiduePairIndex a.q<a.q := hpj.trans_lt hj
  apply Nat.le_antisymm ?_ hpj
  apply Nat.find_min'
  refine ⟨hpLt,?_⟩
  have hs := (Nat.find_spec (exists_lpsResiduePairCandidate a.q)).2
  change ((lpsEffectiveResiduePairIndex a.q/a.q:ℕ):ZMod a.q)^2+
    ((lpsEffectiveResiduePairIndex a.q%a.q:ℕ):ZMod a.q)^2+1=0 at hs
  rw [Nat.div_eq_of_lt hpLt,Nat.mod_eq_of_lt hpLt] at hs
  have hz : (lpsEffectiveResiduePairIndex a.q:ZMod a.q)^2=((a.q-1:ℕ):ZMod a.q) := by
    rw [lpsMinusRoot_natCast]
    norm_num only [Nat.cast_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add] at hs
    linear_combination hs
  apply (ModularTrial.product_eq_iff _ _ (a.q-1) a.q a.prime.pos
    (by have := a.prime.pos;omega)).mpr
  simpa only [pow_two] using hz

/-- The original source residue-pair first coordinate is zero at an LPS residue prime. -/
theorem lpsResidueX_zero_of_residuePrime (a : LPSResiduePrime p) : lpsResidueX a.q=0 := by
  unfold lpsResidueX lpsEffectiveResidueX
  rw [←lpsMinusRoot_pair_index a,Nat.div_eq_of_lt (SquareRoot.index_lt _ _ _)]
  simp

/-- The original source residue-pair second coordinate is the same least numerical root. -/
theorem lpsResidueY_eq_minusRoot (a : LPSResiduePrime p) :
    lpsResidueY a.q=(SquareRoot.index (a.q-1) a.q (lpsMinusRoot_numeric_exists a):ZMod a.q) := by
  unfold lpsResidueY lpsEffectiveResidueY
  rw [←lpsMinusRoot_pair_index a,Nat.mod_eq_of_lt (SquareRoot.index_lt _ _ _)]

end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct.LPSResidueRootMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct
open Turing StateTransition

/-- Actual fixed finite machine for this proved instruction/selector closure. -/
def machine : Machine := Composition.machine (RetainedInput.machine MinusSquareRootInput.machine)
  SquareRoot.machine
/-- Mathematical bound on the actually emitted root-search input length. -/
noncomputable def size : Polynomial ℕ := Polynomial.C 2*Polynomial.X+Polynomial.C 3
/-- Mathematical polynomial derived from the whole actual instruction execution. -/
noncomputable def time : Polynomial ℕ :=
  SquareRoot.time.comp size+Polynomial.C 2*size+Polynomial.C 6*Polynomial.X+Polynomial.C 13

/-- Complete genuine instruction execution satisfies its derived input polynomial. -/
noncomputable def polyExec {p : ℕ} (a : LPSResiduePrime p) :
    EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
      (some (machine.halt (unary (lpsEffectiveResiduePairIndex a.q))))
      (time.eval (unary a.q).length) := by
  have hB := SquareRoot.polyExec (a.q-1) a.q a.prime.pos (lpsMinusRoot_numeric_exists a)
  rw [lpsMinusRoot_pair_index] at hB
  have h := Composition.executes (RetainedInput.machine MinusSquareRootInput.machine) SquareRoot.machine
    _ _ _ _ _ (MinusSquareRootInput.retainedExec a.q a.prime.pos) hB
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hL : (SquareRootAdvance.record (a.q-1) 0 a.q).length≤2*a.q+3 := by
    rw [SquareRootAdvance.record_length]
    omega
  have hp := Composition.polynomial_eval_monotone SquareRoot.time hL
  change SquareRoot.time.eval (SquareRootAdvance.record (a.q-1) 0 a.q).length≤
    SquareRoot.time.eval (2*a.q+3) at hp
  simp only [time,size,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,unary_length]
  omega

/-- Standard Mathlib output certificate from the genuine complete machine execution. -/
noncomputable def outputsInTime {p : ℕ} (a : LPSResiduePrime p) :
    TM2OutputsInTime machine.toFinTM2 (unary a.q)
      (some (unary (lpsEffectiveResiduePairIndex a.q))) (time.eval (unary a.q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec a)

/-- Standard polynomial-time computation using this actual fixed machine and faithful input. -/
noncomputable def computableInPolyTime (p : ℕ) :
    TM2ComputableInPolyTime (fun a:LPSResiduePrime p => unary a.q) unary
      (fun a => lpsEffectiveResiduePairIndex a.q) where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun a => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (unary a.q))
      (some (List.map id (unary (lpsEffectiveResiduePairIndex a.q)))) (time.eval (unary a.q).length)
    have h := outputsInTime a
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h

open scoped MatrixGroups
/-- Actual complete selector execution fits the derived polynomial in the true PSL carrier size. -/
noncomputable def blockExec {p : ℕ} (a : LPSResiduePrime p) :
    EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
      (some (machine.halt (unary (lpsEffectiveResiduePairIndex a.q))))
      (time.eval (2*Fintype.card PSL(2,ZMod a.q))) := by
  have h := polyExec a
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  rw [unary_length]
  exact Composition.polynomial_eval_monotone time a.q_le_two_mul_card_psl

/-- Standard actual selector output certificate at the proved PSL carrier budget. -/
noncomputable def blockOutputsInTime {p : ℕ} (a : LPSResiduePrime p) :
    TM2OutputsInTime machine.toFinTM2 (unary a.q) (some (unary (lpsEffectiveResiduePairIndex a.q)))
      (time.eval (2*Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime machine _ _ _ (blockExec a)

end QEC.Coding.TannerLiftedProduct.LPSResidueRootMachine
