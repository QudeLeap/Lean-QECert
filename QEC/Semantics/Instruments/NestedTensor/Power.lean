import QEC.Semantics.Instruments.Selection.Selection
/-!
# Nested tensor powers of finite instruments

This module iterates the literal finite-instrument tensor-power construction.
At each depth, every current carrier and finite history is tensor-powered by
the same finite branch count.  The nested carrier is kept verbatim, so clients
can lift a physical stage over a growing logical-path tree without introducing
an input-product assumption or an unproved tensor associator.
-/

universe u v w

namespace QEC
namespace Semantics

noncomputable section

namespace FiniteInstrument

/-- The finite raw or observed history obtained by repeatedly taking the same
homogeneous tensor power. -/
def nestedTensorHistory (alpha : Type v) (branches : Nat) : Nat -> Type v
  | 0 => alpha
  | depth + 1 => nestedTensorHistory (tensorPowerHistory alpha branches) branches depth

/-- A leaf path through a recursively nested tensor power.  The newest tensor
coordinate is appended to the path, in the same order as
`nestedTensorHistory` builds its layers. -/
def nestedTensorPath (branches : Nat) : Nat -> Type
  | 0 => PUnit
  | depth + 1 => nestedTensorPath branches depth × Fin branches

instance nestedTensorPathFintype (branches depth : Nat) :
    Fintype (nestedTensorPath branches depth) := by
  induction depth with
  | zero =>
      simpa [nestedTensorPath] using (inferInstance : Fintype PUnit)
  | succ depth ih =>
      simpa [nestedTensorPath] using
        (inferInstance : Fintype (nestedTensorPath branches depth × Fin branches))

/-- Read a recursive nested path as its equivalent finite function of depth
coordinates.  The newest coordinate is appended at `Fin.last`. -/
def nestedTensorPathEquiv (branches : Nat) : (depth : Nat) ->
    nestedTensorPath branches depth ≃ (Fin depth -> Fin branches)
  | 0 =>
      { toFun := fun _ index => Fin.elim0 index
        invFun := fun _ => PUnit.unit
        left_inv := by intro path; exact PUnit.ext _ _
        right_inv := by intro path; funext index; exact Fin.elim0 index }
  | depth + 1 =>
      let previous := nestedTensorPathEquiv branches depth
      { toFun := fun path => Fin.lastCases path.2 (previous path.1)
        invFun := fun path =>
          (previous.symm (fun index => path index.castSucc), path (Fin.last depth))
        left_inv := by
          intro path
          apply Prod.ext
          · exact previous.injective (by
              funext index
              simp)
          · simp
        right_inv := by
          intro path
          funext index
          refine Fin.lastCases ?_ (fun previousIndex => ?_) index
          · simp
          · simp }

/-- A nested path and its finite-function representation select the same
coordinate at every predecessor stage and the same newest coordinate. -/
@[simp] theorem nestedTensorPathEquiv_succ_apply
    (branches depth : Nat) (path : nestedTensorPath branches depth)
    (trial : Fin branches) :
    nestedTensorPathEquiv branches (depth + 1) (path, trial) =
      Fin.lastCases trial (nestedTensorPathEquiv branches depth path) := by
  rfl

/-- The literal recursive nested path carrier has exactly `branches ^ depth`
elements. -/
theorem nestedTensorPath_card (branches depth : Nat) :
    Fintype.card (nestedTensorPath branches depth) = branches ^ depth := by
  rw [Fintype.card_congr (nestedTensorPathEquiv branches depth)]
  simp

/-- Read the leaf selected by an actual path through a recursively nested
tensor history. -/
def nestedTensorHistoryAt (alpha : Type v) (branches : Nat) :
    (depth : Nat) -> nestedTensorHistory alpha branches depth ->
      nestedTensorPath branches depth -> alpha
  | 0, history, _ => history
  | depth + 1, history, path =>
      tensorPowerHistoryAt alpha branches
        (nestedTensorHistoryAt (tensorPowerHistory alpha branches) branches
          depth history path.1)
        path.2

instance nestedTensorHistoryFintype (alpha : Type v) [Fintype alpha]
    (branches depth : Nat) : Fintype (nestedTensorHistory alpha branches depth) := by
  induction depth generalizing alpha with
  | zero =>
      simpa [nestedTensorHistory] using (inferInstance : Fintype alpha)
  | succ depth ih =>
      change Fintype
        (nestedTensorHistory (tensorPowerHistory alpha branches) branches depth)
      exact ih (alpha := tensorPowerHistory alpha branches)

@[reducible] private noncomputable def nestedTensorSystemOf
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : TensorPowerSystem := by
  let normed : NormedAddCommGroup H := inferInstance
  letI : NormedAddCommGroup H := normed
  let inner : InnerProductSpace Complex H := inferInstance
  letI : InnerProductSpace Complex H := inner
  let finite : FiniteQuantumSystem H := inferInstance
  exact
    { carrier := H
      normedAddCommGroup := normed
      innerProductSpace := inner
      finiteDimensional := finite }

/-- The finite-dimensional Hilbert system obtained by repeatedly applying the
literal homogeneous tensor-power carrier construction. -/
@[reducible] noncomputable def nestedTensorSystem
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (branches : Nat) : Nat -> TensorPowerSystem
  | 0 => nestedTensorSystemOf H
  | depth + 1 =>
      let next := tensorPowerSystem H branches
      @nestedTensorSystem next.carrier next.normedAddCommGroup
        next.innerProductSpace next.finiteDimensional branches depth

/-- The literal carrier underlying `nestedTensorSystem`. -/
abbrev nestedTensorCarrier
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (branches depth : Nat) : Type u :=
  (nestedTensorSystem H branches depth).carrier

variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/-- Repeatedly tensor-power a finite instrument over a growing nested carrier.
Depth zero is the supplied instrument; every successor tensor-powers the whole
current instrument by `branches`. -/
noncomputable def nestedTensorPower (I : FiniteInstrument kappa Omega H K)
    (branches depth : Nat) :
    FiniteInstrument
      (nestedTensorHistory kappa branches depth)
      (nestedTensorHistory Omega branches depth)
      (nestedTensorCarrier H branches depth)
      (nestedTensorCarrier K branches depth) := by
  induction depth generalizing kappa Omega H K with
  | zero => exact I
  | succ depth ih => exact ih (I.tensorPower branches)

/-- Completeness is preserved at every nested tensor-power depth. -/
theorem nestedTensorPower_complete (I : FiniteInstrument kappa Omega H K)
    (hI : I.kraus.Complete) (branches depth : Nat) :
    (nestedTensorPower I branches depth).kraus.Complete := by
  induction depth generalizing kappa Omega H K with
  | zero => exact hI
  | succ depth ih =>
      exact ih (I.tensorPower branches) (I.tensorPower_complete hI branches)

/-- A complete nested tensor power has normalized total observable Born mass
for every density operator on its literal nested input carrier. -/
theorem nestedTensorPower_sum_bornWeight_eq_one
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (branches depth : Nat)
    (rho : DensityOperator (nestedTensorCarrier H branches depth)) :
    ∑ outcome, (nestedTensorPower I branches depth).bornWeight outcome rho = 1 :=
  (nestedTensorPower I branches depth).sum_bornWeight_eq_one
    (nestedTensorPower_complete I hI branches depth) rho

end FiniteInstrument

end

end Semantics
end QEC
