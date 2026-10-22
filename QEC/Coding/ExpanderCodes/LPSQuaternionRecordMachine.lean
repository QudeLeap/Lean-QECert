import QEC.Coding.BitTuring.UnarySignedCoefficient
import QEC.Coding.BitTuring.ModulusQuery
import QEC.Coding.BitTuring.BitDelimiters
import QEC.Coding.ExpanderCodes.LPSInverseMachine
import QEC.Coding.ExpanderCodes.LPSMatrixProductMachine

/-!
# Actual q-only original quaternion initialization

For fixed p and a fixed original norm-p quaternion, this complete finite program accepts only
unary q. An actual q delimiter and six actual retained queries emit the canonical original
scalar, original residue Y, d,c,b,a and q. Original norm/large-prime facts derive the signed
coefficient domain; the whole actual run derives unary polynomial and true PSL-carrier time.
Faithful input and standard certificates retain the original source data and exact matrix
coordinate convention. This supplies initialization for subsequent actual quaternion matrix
assembly; complete normalized matrix/generator emission, ordered PSL indexing, sparse CSS
runtime and strong arithmetic growth remain unproved. The exact public PK22 theorem remains
unrealized. Bool is the encoding alphabet, not a restriction on the code field.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open FieldProjection
/-- Mathematical original signed coordinate values; they never control program instructions. -/
def coordinates {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) :=
  [(t.a:ZMod a.q).val,(t.b:ZMod a.q).val,(t.c:ZMod a.q).val,(t.d:ZMod a.q).val]
/-- Whole output record keeps original q and all actual results for later matrix assembly. -/
def record {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) := stream
  [LPSDegreeInverseMachine.scalar a,lpsEffectiveResiduePairIndex a.q,
   (t.d:ZMod a.q).val,(t.c:ZMod a.q).val,(t.b:ZMod a.q).val,(t.a:ZMod a.q).val,a.q]
/-- Fixed p/t determine finite literal instructions; the varying family member supplies only q. -/
def machine (p:ℕ) (t:LPSQuaternion) := Composition.machine BitDelimiter.machine
  (Composition.machine (ModulusQuery.machine 0 (SignedCoefficient.machine t.a))
   (Composition.machine (ModulusQuery.machine 1 (SignedCoefficient.machine t.b))
    (Composition.machine (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
     (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
      (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
       (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p)))))))
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def bodyTime (p:ℕ) (t:LPSQuaternion) : Polynomial ℕ :=
  SignedCoefficient.time t.a+SignedCoefficient.time t.b+SignedCoefficient.time t.c+SignedCoefficient.time t.d+
  LPSResidueRootMachine.time+LPSDegreeInverseMachine.time p
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def size : Polynomial ℕ := Polynomial.C 6*(Polynomial.X+1)
/-- Actual finite program, proved transition invariant or certificate in the complete closure. -/
noncomputable def time (p:ℕ) (t:LPSQuaternion) : Polynomial ℕ :=
  (bodyTime p t).comp size+Polynomial.C 1000*(Polynomial.X+1)
/-- Original norm-p bounds make every fixed coefficient canonical at the actual varying prime. -/
theorem coordinate_bounds {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    t.a.natAbs<a.q ∧ t.b.natAbs<a.q ∧ t.c.natAbs<a.q ∧ t.d.natAbs<a.q := by
  have h:=coordinate_bounds_of_norm a.degreePrime.pos t ht
  have hp:(p:ℤ)<a.q := by exact_mod_cast (show p<a.q by have := a.large;omega)
  have ha:|t.a|<(a.q:ℤ):=(abs_le.mpr ⟨h.1,h.2.1⟩).trans_lt hp
  have hb:|t.b|<(a.q:ℤ):=(abs_le.mpr ⟨h.2.2.1,h.2.2.2.1⟩).trans_lt hp
  have hc:|t.c|<(a.q:ℤ):=(abs_le.mpr ⟨h.2.2.2.2.1,h.2.2.2.2.2.1⟩).trans_lt hp
  have hd:|t.d|<(a.q:ℤ):=(abs_le.mpr ⟨h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2⟩).trans_lt hp
  rw [←Int.natCast_natAbs] at ha hb hc hd
  exact ⟨by exact_mod_cast ha,by exact_mod_cast hb,by exact_mod_cast hc,by exact_mod_cast hd⟩
/-- Source-specific true execution of each fixed signed coefficient, not supplied field values. -/
noncomputable def coefficientExec {p:ℕ} (a:LPSResiduePrime p) (c:ℤ) (hc:c.natAbs<a.q) :
    EvalsToInTime (TM2.step (SignedCoefficient.machine c).program)
      ((SignedCoefficient.machine c).init (unary a.q))
      (some ((SignedCoefficient.machine c).halt (unary (c:ZMod a.q).val)))
      ((SignedCoefficient.time c).eval a.q) := by
  have h:=SignedCoefficient.exec c a.q hc
  rw [SignedCoefficient.output_eq_val c a.q a.prime.pos hc,unary_length] at h
  exact h
/-- Entire actual q-only six-query program preserves all original canonical values in one run. -/
noncomputable def exec {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) := by
  let : NeZero a.q:=⟨a.prime.ne_zero⟩
  let A:=(t.a:ZMod a.q).val
  let B:=(t.b:ZMod a.q).val
  let C:=(t.c:ZMod a.q).val
  let D:=(t.d:ZMod a.q).val
  let Y:=lpsEffectiveResiduePairIndex a.q
  let S:=LPSDegreeInverseMachine.scalar a
  have hb:=coordinate_bounds a t ht
  have hY:Y<a.q := by
    dsimp only [Y]
    rw [←lpsMinusRoot_pair_index a]
    exact SquareRoot.index_lt _ _ _
  have hS:S<a.q:=ZMod.val_lt _
  have h0:=ModulusQuery.exec 0 (SignedCoefficient.machine t.a) (SignedCoefficient.time t.a)
    [a.q] (by simp) a.q A (ZMod.val_lt _)
    (by simp [fields,maskAt,ModulusQuery.mask]) (coefficientExec a t.a hb.1)
  have h1:=ModulusQuery.exec 1 (SignedCoefficient.machine t.b) (SignedCoefficient.time t.b)
    [A,a.q] (by simp) a.q B (ZMod.val_lt _)
    (by simp [fields,maskAt,ModulusQuery.mask]) (coefficientExec a t.b hb.2.1)
  have h2:=ModulusQuery.exec 2 (SignedCoefficient.machine t.c) (SignedCoefficient.time t.c)
    [B,A,a.q] (by simp) a.q C (ZMod.val_lt _)
    (by simp [fields,maskAt,ModulusQuery.mask]) (coefficientExec a t.c hb.2.2.1)
  have h3:=ModulusQuery.exec 3 (SignedCoefficient.machine t.d) (SignedCoefficient.time t.d)
    [C,B,A,a.q] (by simp) a.q D (ZMod.val_lt _)
    (by simp [fields,maskAt,ModulusQuery.mask]) (coefficientExec a t.d hb.2.2.2)
  have h4:=ModulusQuery.exec 4 LPSResidueRootMachine.machine LPSResidueRootMachine.time
    [D,C,B,A,a.q] (by simp) a.q Y hY
    (by simp [fields,maskAt,ModulusQuery.mask]) (by simpa only [unary_length] using LPSResidueRootMachine.polyExec a)
  have h5:=ModulusQuery.exec 5 (LPSDegreeInverseMachine.machine p) (LPSDegreeInverseMachine.time p)
    [Y,D,C,B,A,a.q] (by simp) a.q S hS
    (by simp [fields,maskAt,ModulusQuery.mask]) (by simpa only [unary_length] using LPSDegreeInverseMachine.polyExec a)
  have h45:=Composition.executes (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
    (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p)) _ _ _ _ _ h4 h5
  have h345:=Composition.executes (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
    (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
      (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p))) _ _ _ _ _ h3 h45
  have h2345:=Composition.executes (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
    (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
      (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
       (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p)))) _ _ _ _ _ h2 h345
  have h12345:=Composition.executes (ModulusQuery.machine 1 (SignedCoefficient.machine t.b))
    (Composition.machine (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
     (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
      (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
       (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p))))) _ _ _ _ _ h1 h2345
  have h012345:=Composition.executes (ModulusQuery.machine 0 (SignedCoefficient.machine t.a))
    (Composition.machine (ModulusQuery.machine 1 (SignedCoefficient.machine t.b))
     (Composition.machine (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
      (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
       (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
        (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p)))))) _ _ _ _ _ h0 h12345
  have hd:=BitDelimiter.exec (unary a.q)
  rw [show unary a.q++[false]=stream [a.q] by simp [stream]] at hd
  exact Composition.executes BitDelimiter.machine
    (Composition.machine (ModulusQuery.machine 0 (SignedCoefficient.machine t.a))
     (Composition.machine (ModulusQuery.machine 1 (SignedCoefficient.machine t.b))
      (Composition.machine (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
       (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
        (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
         (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p))))))) _ _ _ _ _ hd h012345

/-- Complete actual clean q-only initialization at its derived whole-program polynomial. -/
noncomputable def polyExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    EvalsToInTime (TM2.step (machine p t).program) ((machine p t).init (unary a.q))
      (some ((machine p t).halt (record a t))) ((time p t).eval (unary a.q).length) := by
  have h:=exec a t ht
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  let : NeZero a.q:=⟨a.prime.ne_zero⟩
  let A:=(t.a:ZMod a.q).val
  let B:=(t.b:ZMod a.q).val
  let C:=(t.c:ZMod a.q).val
  let D:=(t.d:ZMod a.q).val
  let Y:=lpsEffectiveResiduePairIndex a.q
  have hA:A<a.q:=ZMod.val_lt _
  have hB:B<a.q:=ZMod.val_lt _
  have hC:C<a.q:=ZMod.val_lt _
  have hD:D<a.q:=ZMod.val_lt _
  have hY:Y<a.q := by
    dsimp only [Y]
    rw [←lpsMinusRoot_pair_index a]
    exact SquareRoot.index_lt _ _ _
  have hL0:(stream [a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp0:(SignedCoefficient.time t.a).eval (stream [a.q]).length≤(SignedCoefficient.time t.a).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (SignedCoefficient.time t.a) hL0
  have hL1:(stream [A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp1:(SignedCoefficient.time t.b).eval (stream [A,a.q]).length≤(SignedCoefficient.time t.b).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (SignedCoefficient.time t.b) hL1
  have hL2:(stream [B,A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp2:(SignedCoefficient.time t.c).eval (stream [B,A,a.q]).length≤(SignedCoefficient.time t.c).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (SignedCoefficient.time t.c) hL2
  have hL3:(stream [C,B,A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp3:(SignedCoefficient.time t.d).eval (stream [C,B,A,a.q]).length≤(SignedCoefficient.time t.d).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (SignedCoefficient.time t.d) hL3
  have hL4:(stream [D,C,B,A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp4:(LPSResidueRootMachine.time).eval (stream [D,C,B,A,a.q]).length≤(LPSResidueRootMachine.time).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (LPSResidueRootMachine.time) hL4
  have hL5:(stream [Y,D,C,B,A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp5:(LPSDegreeInverseMachine.time p).eval (stream [Y,D,C,B,A,a.q]).length≤(LPSDegreeInverseMachine.time p).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (LPSDegreeInverseMachine.time p) hL5

  change (ModulusQuery.time (LPSDegreeInverseMachine.time p)).eval (stream [Y,D,C,B,A,a.q]).length+
    (2*(stream [Y,D,C,B,A,a.q]).length+2)+
    (ModulusQuery.time LPSResidueRootMachine.time).eval (stream [D,C,B,A,a.q]).length+
    (2*(stream [D,C,B,A,a.q]).length+2)+
    (ModulusQuery.time (SignedCoefficient.time t.d)).eval (stream [C,B,A,a.q]).length+
    (2*(stream [C,B,A,a.q]).length+2)+
    (ModulusQuery.time (SignedCoefficient.time t.c)).eval (stream [B,A,a.q]).length+
    (2*(stream [B,A,a.q]).length+2)+
    (ModulusQuery.time (SignedCoefficient.time t.b)).eval (stream [A,a.q]).length+
    (2*(stream [A,a.q]).length+2)+
    (ModulusQuery.time (SignedCoefficient.time t.a)).eval (stream [a.q]).length+
    (2*(stream [a.q]).length+2)+(2*(unary a.q).length+3)≤(time p t).eval (unary a.q).length
  simp only [time,bodyTime,size,ModulusQuery.time,Polynomial.eval_comp,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,unary_length]
  omega

/-- Standard original source record output from the actual q-only program. -/
noncomputable def outputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    TM2OutputsInTime (machine p t).toFinTM2 (unary a.q) (some (record a t))
      ((time p t).eval (unary a.q).length) :=
  Machine.outputsInTime (machine p t) _ _ _ (polyExec a t ht)
/-- Standard computability of original source initialization, with all results computed from q. -/
noncomputable def computableInPolyTime (p:ℕ) (t:LPSQuaternion) (ht:t.norm=p) :
    TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>record a t) where
  tm:=(machine p t).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time p t
  outputsFun:=fun a=>by
    change TM2OutputsInTime (machine p t).toFinTM2 (List.map id (unary a.q))
      (some (List.map id (record a t))) ((time p t).eval (unary a.q).length)
    have h:=outputsInTime a t ht
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
open scoped MatrixGroups
/-- Whole actual initialization at its true original PSL carrier cardinality budget. -/
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    EvalsToInTime (TM2.step (machine p t).program) ((machine p t).init (unary a.q))
      (some ((machine p t).halt (record a t))) ((time p t).eval (2*Fintype.card PSL(2,ZMod a.q))) := by
  have h:=polyExec a t ht
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  rw [unary_length]
  exact Composition.polynomial_eval_monotone (time p t) a.q_le_two_mul_card_psl
/-- Standard true carrier-budget output of the full q-only initialization. -/
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    TM2OutputsInTime (machine p t).toFinTM2 (unary a.q) (some (record a t))
      ((time p t).eval (2*Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime (machine p t) _ _ _ (blockExec a t ht)

/-- The actually selected original Y index is already its canonical field value. -/
theorem residue_index_eq_val {p:ℕ} (a:LPSResiduePrime p) :
    lpsEffectiveResiduePairIndex a.q=(lpsResidueY a.q).val := by
  let : NeZero a.q:=⟨a.prime.ne_zero⟩
  have hy:lpsEffectiveResiduePairIndex a.q<a.q := by
    rw [←lpsMinusRoot_pair_index a]
    exact SquareRoot.index_lt _ _ _
  simp only [lpsResidueY,lpsEffectiveResidueY,ZMod.val_natCast,Nat.mod_eq_of_lt hy]
/-- All seven record fields are exact original source data, in the documented retention order. -/
theorem record_eq_source {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) :
    record a t=stream ([((lpsEffectiveDegreeRoot a)⁻¹).val,(lpsResidueY a.q).val]++
      (coordinates a t).reverse++[a.q]) := by
  rw [←residue_index_eq_val a]
  simp [record,coordinates,LPSDegreeInverseMachine.scalar]
/-- Source input encoding remains faithful to the growing original family member. -/
theorem input_injective (p:ℕ) : Function.Injective (fun a:LPSResiduePrime p=>unary a.q) :=
  lpsResiduePrime_unary_injective p
/-- Exact original matrix coordinate convention to be consumed by the next actual assembly. -/
theorem original_matrix_fields {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) :
    LPSMatrixProductMachine.fields a.q (lpsQuaternionMatrix a.q t)=
      [((t.a:ZMod a.q)+(t.d:ZMod a.q)*lpsResidueY a.q).val,
       (-(t.b:ZMod a.q)*lpsResidueY a.q+(t.c:ZMod a.q)).val,
       (-(t.b:ZMod a.q)*lpsResidueY a.q-(t.c:ZMod a.q)).val,
       ((t.a:ZMod a.q)-(t.d:ZMod a.q)*lpsResidueY a.q).val] := by
  simp [LPSMatrixProductMachine.fields,lpsQuaternionMatrix,lpsResidueX_zero_of_residuePrime a]
end QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine
