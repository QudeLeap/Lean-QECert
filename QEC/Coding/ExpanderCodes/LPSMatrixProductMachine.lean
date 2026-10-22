import QEC.Coding.BitTuring.UnaryMatrixProduct
import QEC.Coding.ExpanderCodes.LPSInverseMachine
import QEC.Coding.ExpanderCodes.LPSVertexEnumeration

/-!
# Actual original LPS matrix product emission

The complete actual Boolean program emits the four canonical entries of the exact original
lpsEntryMatrix product and SL multiplication. True canonical input lengths and the original
q-to-PSL-cardinality bound derive a PSL-carrier polynomial budget. Graph arithmetic modulus
is distinct from the arbitrary code field. This internal closure leaves original PSL indexing,
normalization-matrix emission, sparse CSS runtime and strong arithmetic growth unproved;
it does not realize the exact public PK22 main theorem.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
open scoped MatrixGroups

/-- Mathematical row-major or selected-field specification, never machine control. -/
def fields (q:ℕ) (A:Matrix (Fin 2) (Fin 2) (ZMod q)) : List ℕ :=
  [(A 0 0).val,(A 0 1).val,(A 1 0).val,(A 1 1).val]
/-- Encode every varying operand and the original modulus on the input tape. -/
def input (q:ℕ) (A B:Matrix (Fin 2) (Fin 2) (ZMod q)) : List Bool :=
  FieldProjection.stream (fields q A++fields q B++[q])
/-- Mathematical specification of the actual emitted result, never a program callback. -/
def output (q:ℕ) (A B:Matrix (Fin 2) (Fin 2) (ZMod q)) : List Bool :=
  FieldProjection.raw (fields q (A*B))

/-- Canonical emitted values equal the true finite-field matrix product. -/
theorem product_fields (q:ℕ) (hq:0<q) (A B:Matrix (Fin 2) (Fin 2) (ZMod q)) :
    fields q (A*B)=
      [((A 0 0).val*(B 0 0).val+(A 0 1).val*(B 1 0).val)%q,
       ((A 0 0).val*(B 0 1).val+(A 0 1).val*(B 1 1).val)%q,
       ((A 1 0).val*(B 0 0).val+(A 1 1).val*(B 1 0).val)%q,
       ((A 1 0).val*(B 0 1).val+(A 1 1).val*(B 1 1).val)%q] := by
  let : NeZero q:=⟨hq.ne'⟩
  have hv (x y z w:ZMod q) : (x*y+z*w).val=(x.val*y.val+z.val*w.val)%q := by
    have hc:((x.val*y.val+z.val*w.val:ℕ):ZMod q)=x*y+z*w := by
      simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val]
    rw [←hc,ZMod.val_natCast]
  simp only [fields,Matrix.mul_apply,Fin.sum_univ_two,hv]

/-- Complete actual clean execution at the proved encoded-input polynomial budget. -/
noncomputable def polyExec (q:ℕ) (hq:0<q) (A B:Matrix (Fin 2) (Fin 2) (ZMod q)) :
    EvalsToInTime (TM2.step ModularMatrixProduct.productMachine.program)
      (ModularMatrixProduct.productMachine.init (input q A B))
      (some (ModularMatrixProduct.productMachine.halt (output q A B)))
      (ModularMatrixProduct.time.eval (input q A B).length) := by
  have h:=ModularMatrixProduct.polyExec (A 0 0).val (A 0 1).val (A 1 0).val (A 1 1).val
    (B 0 0).val (B 0 1).val (B 1 0).val (B 1 1).val q hq
  rw [output,product_fields q hq]
  simpa only [input,fields,List.cons_append,List.nil_append] using h

/-- Standard Mathlib output certificate from the whole actual execution. -/
noncomputable def outputsInTime (q:ℕ) (hq:0<q) (A B:Matrix (Fin 2) (Fin 2) (ZMod q)) :
    TM2OutputsInTime ModularMatrixProduct.productMachine.toFinTM2 (input q A B)
      (some (output q A B)) (ModularMatrixProduct.time.eval (input q A B).length) :=
  Machine.outputsInTime ModularMatrixProduct.productMachine _ _ _ (polyExec q hq A B)

/-- Exact original LPS entry-matrix product, with unchanged coordinates. -/
theorem entryMatrix_product_fields (q:ℕ) (hq:0<q) (a b c d e f g h:Fin q) :
    fields q (lpsEntryMatrix q a b c d*lpsEntryMatrix q e f g h)=
      [(a.val*e.val+b.val*g.val)%q,(a.val*f.val+b.val*h.val)%q,
       (c.val*e.val+d.val*g.val)%q,(c.val*f.val+d.val*h.val)%q] := by
  let : NeZero q:=⟨hq.ne'⟩
  simpa [lpsEntryMatrix,ZMod.val_natCast,Nat.mod_eq_of_lt] using
    product_fields q hq (lpsEntryMatrix q a b c d) (lpsEntryMatrix q e f g h)

/-- Proved actual execution phase or mathematical tape invariant for the complete program. -/
theorem fields_injective (q:ℕ) (hq:0<q) : Function.Injective (fields q) := by
  let : NeZero q:=⟨hq.ne'⟩
  intro A B h
  simp only [fields,List.cons.injEq] at h
  rcases h with ⟨h00,h01,h10,h11,_⟩
  ext i j;fin_cases i <;> fin_cases j <;> exact ZMod.val_injective q (by assumption)

/-- Complete actual execution emits the original SL product matrix entries. -/
noncomputable def slExec (q:ℕ) (hq:0<q) (A B:SL(2,ZMod q)) :
    EvalsToInTime (TM2.step ModularMatrixProduct.productMachine.program)
      (ModularMatrixProduct.productMachine.init (input q A.val B.val))
      (some (ModularMatrixProduct.productMachine.halt (FieldProjection.raw (fields q (A*B).val))))
      (ModularMatrixProduct.time.eval (input q A.val B.val).length) :=
  polyExec q hq A.val B.val

/-- Actual source runtime polynomial in the true PSL carrier cardinality. -/
noncomputable def carrierTime : Polynomial ℕ := ModularMatrixProduct.time.comp
  (Polynomial.C 18*Polynomial.X+Polynomial.C 9)

/-- Complete actual source execution at the true PSL-carrier polynomial budget. -/
noncomputable def carrierExec {p:ℕ} (a:LPSResiduePrime p) (A B:SL(2,ZMod a.q)) :
    EvalsToInTime (TM2.step ModularMatrixProduct.productMachine.program)
      (ModularMatrixProduct.productMachine.init (input a.q A.val B.val))
      (some (ModularMatrixProduct.productMachine.halt (FieldProjection.raw (fields a.q (A*B).val))))
      (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))) := by
  have h:=slExec a.q a.prime.pos A B
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  let : NeZero a.q:=⟨a.prime.pos.ne'⟩
  have hbound:(input a.q A.val B.val).length≤18*Fintype.card PSL(2,ZMod a.q)+9 := by
    have hq:=a.q_le_two_mul_card_psl
    have h00:=ZMod.val_lt (A.val 0 0)
    have h01:=ZMod.val_lt (A.val 0 1)
    have h10:=ZMod.val_lt (A.val 1 0)
    have h11:=ZMod.val_lt (A.val 1 1)
    have h20:=ZMod.val_lt (B.val 0 0)
    have h21:=ZMod.val_lt (B.val 0 1)
    have h30:=ZMod.val_lt (B.val 1 0)
    have h31:=ZMod.val_lt (B.val 1 1)
    simp only [input,fields,List.cons_append,List.nil_append,FieldProjection.stream_length,
      List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  simp only [carrierTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  exact Composition.polynomial_eval_monotone ModularMatrixProduct.time hbound

end QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine
namespace QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
open scoped MatrixGroups
/-- Standard actual original SL matrix output certificate. -/
noncomputable def slOutputsInTime (q:ℕ) (hq:0<q) (A B:SL(2,ZMod q)) :
    TM2OutputsInTime ModularMatrixProduct.productMachine.toFinTM2 (input q A.val B.val)
      (some (FieldProjection.raw (fields q (A*B).val)))
      (ModularMatrixProduct.time.eval (input q A.val B.val).length) :=
  Machine.outputsInTime ModularMatrixProduct.productMachine _ _ _ (slExec q hq A B)
/-- Standard actual output certificate at the proved PSL-carrier budget. -/
noncomputable def carrierOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (A B:SL(2,ZMod a.q)) :
    TM2OutputsInTime ModularMatrixProduct.productMachine.toFinTM2 (input a.q A.val B.val)
      (some (FieldProjection.raw (fields a.q (A*B).val)))
      (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime ModularMatrixProduct.productMachine _ _ _ (carrierExec a A B)
end QEC.Coding.TannerLiftedProduct.LPSMatrixProductMachine
