import QEC.Coding.BitTuring.UnaryRetainedPrefixQuery
import QEC.Coding.ExpanderCodes.LPSSLDeterminantMachine
import QEC.Coding.ExpanderCodes.LPSPSLEqualityMachine

/-!
# Actual original SL and PSL predicates with retained dynamic context

The real prefix/drain/delimiter/retention compiler executes the original determinant-one
candidate and original PSL sign-quotient equality programs on fixed row-major headers. For
arbitrary trailing Boolean context it returns the exact original source predicate flag and the
complete unchanged input, with derived whole polynomial budget, faithful joint encodings and
standard Mathlib certificates. SL inputs need only q>1 and canonical entries; PSL inputs use
prime q and original SL representatives, including characteristic two. No predicate answer,
wrapper execution or runtime witness is supplied. Original lpsSLList filtering and lpsPSLList
last-occurrence dedup/index are the two immediate consumers. Full enumeration/dedup/index,
whole sparse CSS runtime and strong arithmetic spectral growth remain obligations. Original
ordering/representatives and arbitrary-field/every-rate/explicit/cofinal/uniform-locality/
two-sided-distance PK22 scope are preserved; the public theorem remains unproved. Bool is
only the tape alphabet.
-/

namespace QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
def slMachine:=QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery.queryMachine 4 DeterminantPredicate.predicateMachine
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
def slFields (q:ℕ) (x:Fin q×Fin q×Fin q×Fin q):List ℕ:=[x.1.val,x.2.1.val,x.2.2.1.val,x.2.2.2.val,q]
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
def slInput (q:ℕ) (x:(Fin q×Fin q×Fin q×Fin q)×List Bool):List Bool:=stream (slFields q x.1)++x.2
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
def slOutput (q:ℕ) (x:(Fin q×Fin q×Fin q×Fin q)×List Bool):List Bool:=
  LPSSLDeterminantMachine.sourceOutput q x.1++slInput q x
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
noncomputable def slTime:Polynomial ℕ:=QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery.time DeterminantPredicate.predicateTime
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
noncomputable def slExec (q:ℕ) (hq:1<q) (x:(Fin q×Fin q×Fin q×Fin q)×List Bool):
    EvalsToInTime (TM2.step slMachine.program) (slMachine.init (slInput q x))
      (some (slMachine.halt (slOutput q x))) (slTime.eval (slInput q x).length):=
  QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery.queryExec 4 DeterminantPredicate.predicateMachine (slFields q x.1) (by simp [slFields]) x.2 _ _
    (LPSSLDeterminantMachine.sourceExec q hq x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2)
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
theorem slInput_injective (q:ℕ):Function.Injective (slInput q):=by
  intro x y h
  have he:=QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.stream_suffix_injective (slFields q x.1) (slFields q y.1) x.2 y.2
    (by simp [slFields]) h
  have hi:LPSSLDeterminantMachine.sourceInput q x.1=LPSSLDeterminantMachine.sourceInput q y.1:=congrArg stream he.1
  exact Prod.ext (LPSSLDeterminantMachine.sourceInput_injective q hi) he.2
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
theorem slOutput_eq_candidate (q:ℕ) (hq:1<q) (x:(Fin q×Fin q×Fin q×Fin q)×List Bool):
    slOutput q x=[(lpsSLMatrixCandidate q x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2).isSome]++slInput q x:=by
  have h:decide ((lpsEntryMatrix q x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2).det=1)=
      (lpsSLMatrixCandidate q x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2).isSome:=
    (LPSSLDeterminantMachine.predicate_eq_source q hq _ _ _ _).symm.trans
      (LPSSLDeterminantMachine.predicate_eq_candidate q hq _ _ _ _)
  simp only [slOutput,LPSSLDeterminantMachine.sourceOutput,h]
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
noncomputable def slComputableInPolyTime (q:ℕ) (hq:1<q):
    TM2ComputableInPolyTime (slInput q) id (slOutput q) where
  tm:=slMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=slTime
  outputsFun:=fun x=>by
    change TM2OutputsInTime slMachine.toFinTM2 (List.map id (slInput q x))
      (some (List.map id (slOutput q x))) (slTime.eval (slInput q x).length)
    have h:=Machine.outputsInTime slMachine _ _ _ (slExec q hq x)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h

/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
def pslMachine:=QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery.queryMachine 8 PSLComparison.predicateMachine
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
def pslFields (q:ℕ) (x:SL(2,ZMod q)×SL(2,ZMod q)):List ℕ:=
  LPSMatrixProductMachine.fields q x.1.val++LPSMatrixProductMachine.fields q x.2.val++[q]
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
def pslInput (q:ℕ) (x:(SL(2,ZMod q)×SL(2,ZMod q))×List Bool):List Bool:=stream (pslFields q x.1)++x.2
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
def pslOutput (q:ℕ) [Fact q.Prime] (x:(SL(2,ZMod q)×SL(2,ZMod q))×List Bool):List Bool:=
  LPSPSLEqualityMachine.output q x.1.1 x.1.2++pslInput q x
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
noncomputable def pslTime:Polynomial ℕ:=QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery.time PSLComparison.time
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
noncomputable def pslExec (q:ℕ) [Fact q.Prime] (x:(SL(2,ZMod q)×SL(2,ZMod q))×List Bool):
    EvalsToInTime (TM2.step pslMachine.program) (pslMachine.init (pslInput q x))
      (some (pslMachine.halt (pslOutput q x))) (pslTime.eval (pslInput q x).length):=by
  letI:=lpsPSLDecidableEq q
  have hh:=QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery.queryExec 8 PSLComparison.predicateMachine (pslFields q x.1)
    (by simp [pslFields,LPSMatrixProductMachine.fields]) x.2
    (decide ((QuotientGroup.mk x.1.1:PSL(2,ZMod q))=QuotientGroup.mk x.1.2)) PSLComparison.time
    (LPSPSLEqualityMachine.exec q x.1.1 x.1.2)
  exact hh
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
theorem pslInput_injective (q:ℕ) (hq:0<q):Function.Injective (pslInput q):=by
  intro x y h
  have he:=QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.stream_suffix_injective (pslFields q x.1) (pslFields q y.1) x.2 y.2
    (by simp [pslFields,LPSMatrixProductMachine.fields]) h
  have hi:LPSPSLEqualityMachine.input q x.1.1 x.1.2=LPSPSLEqualityMachine.input q y.1.1 y.1.2:=congrArg stream he.1
  exact Prod.ext (LPSPSLEqualityMachine.input_injective q hq hi) he.2
/-- Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate. -/
noncomputable def pslComputableInPolyTime (q:ℕ) [Fact q.Prime]:
    TM2ComputableInPolyTime (pslInput q) id (pslOutput q) where
  tm:=pslMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=pslTime
  outputsFun:=fun x=>by
    change TM2OutputsInTime pslMachine.toFinTM2 (List.map id (pslInput q x))
      (some (List.map id (pslOutput q x))) (pslTime.eval (pslInput q x).length)
    have h:=Machine.outputsInTime pslMachine _ _ _ (pslExec q x)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
end QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries
