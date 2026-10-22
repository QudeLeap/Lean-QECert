import QEC.Semantics.Instruments.Branches.BranchOperatorLinear
import QEC.Semantics.Instruments.NestedTensor.FilteredMarginalBranchOperator
import QEC.Semantics.Instruments.Sequential.FilteredBranchOperator
/-!
# Selected nested marginals of sequential filtered branch events

This source-neutral bridge filters a predecessor observation and one selected
leaf observation of a sequentially appended nested tensor stage.  After every
sibling history is summed and the selected output leaf is retained, the result
is the local filtered base-stage branch sum applied to the selected
unnormalized predecessor event operator.  No normalization or product-state
premise is used.
-/

universe u v w x y

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators

noncomputable section

namespace FiniteInstrument

variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

/-- Selecting a successor-depth nested leaf is the preceding nested
coordinate followed by the newest tensor coordinate. -/
theorem nestedTensorCoordinateOperator_succ
    (L : Type u) [NormedAddCommGroup L] [InnerProductSpace Complex L]
    [FiniteQuantumSystem L] (branches depth : Nat)
    (path : nestedTensorPath branches depth) (port : Fin branches)
    (A : Operator (nestedTensorCarrier L branches (depth + 1))) :
    nestedTensorCoordinateOperator L branches (depth + 1) (path, port) A =
      tensorPowerCoordinateOperator branches port
        (nestedTensorCoordinateOperator
          (tensorPowerCarrier L branches) branches depth path A) := by
  rfl

/-- The unnormalized branch operator obtained by retaining one local event. -/
noncomputable def filteredBranchOperatorSum
    (J : FiniteInstrument kappaTwo Xi K L)
    (predicate : Xi -> Prop) [DecidablePred predicate]
    (A : Operator K) : Operator L :=
  ∑ outcome : Xi,
    if predicate outcome then J.branchOperator outcome A else 0

/-- The named filtered branch operator is complex-linear in its
unnormalized input. -/
theorem filteredBranchOperatorSum_smul
    (J : FiniteInstrument kappaTwo Xi K L)
    (predicate : Xi -> Prop) [DecidablePred predicate]
    (c : Complex) (A : Operator K) :
    filteredBranchOperatorSum J predicate (c • A) =
      c • filteredBranchOperatorSum J predicate A := by
  classical
  unfold filteredBranchOperatorSum
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases houtcome : predicate outcome
  · simp only [houtcome, if_true]
    exact branchOperator_smul J outcome c A
  · simp [houtcome]

/-- On a density input, the real trace of a filtered branch operator is the
literal filtered Born-mass sum. -/
theorem filteredBranchOperatorSum_trace_re_eq_bornWeight_sum
    (J : FiniteInstrument kappaTwo Xi K L)
    (predicate : Xi -> Prop) [DecidablePred predicate]
    (rho : DensityOperator K) :
    Complex.re (LinearMap.trace Complex L
      (filteredBranchOperatorSum J predicate rho.toOperator)) =
      ∑ outcome ∈ Finset.univ.filter predicate,
        J.bornWeight outcome rho := by
  classical
  unfold filteredBranchOperatorSum bornWeight
  rw [Finset.sum_filter, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases houtcome : predicate outcome <;> simp [houtcome]

/-- Scaling a density operator by a real mass scales the real trace of every
filtered branch event by that same mass. -/
theorem filteredBranchOperatorSum_trace_re_smul_real
    (J : FiniteInstrument kappaTwo Xi K L)
    (predicate : Xi -> Prop) [DecidablePred predicate]
    (mass : Real) (rho : DensityOperator K) :
    Complex.re (LinearMap.trace Complex L
      (filteredBranchOperatorSum J predicate
        ((mass : Complex) • rho.toOperator))) =
      mass * ∑ outcome ∈ Finset.univ.filter predicate,
        J.bornWeight outcome rho := by
  rw [filteredBranchOperatorSum_smul,
    map_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [filteredBranchOperatorSum_trace_re_eq_bornWeight_sum]

/-- The selected nested coordinate of an unnormalized filtered predecessor
event. -/
noncomputable def nestedFilteredPredecessorCoordinateOperator
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (path : nestedTensorPath branches depth)
    (A : Operator H) : Operator K :=
  nestedTensorCoordinateOperator K branches depth path
    (∑ outcome : Omega,
      if predicate outcome then I.branchOperator outcome A else 0)

/-- The selected nested coordinate of a sequential event that retains one
predecessor event and one local event at that coordinate. -/
noncomputable def bindNestedFilteredCoordinateOperator
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (path : nestedTensorPath branches depth)
    (A : Operator H) : Operator L :=
  nestedTensorCoordinateOperator L branches depth path
    (∑ outcome : Sigma fun _ : Omega => nestedTensorHistory Xi branches depth,
      if firstPredicate outcome.1 ∧
          secondPredicate
            (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
        (I.bind (fun _ => nestedTensorPower J branches depth)).branchOperator
          outcome A
      else 0)

/-- A selected nested leaf of a sequential filtered event depends only on the
selected unnormalized predecessor event operator and the local filtered base
stage at that leaf. -/
theorem bind_nestedTensor_coordinateOperator_branchOperator_filter_sum_eq
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L) (hJ : J.kraus.Complete)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (path : nestedTensorPath branches depth)
    (A : Operator H) :
    nestedTensorCoordinateOperator L branches depth path
        (∑ outcome : Sigma fun _ : Omega => nestedTensorHistory Xi branches depth,
          if firstPredicate outcome.1 ∧
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
            (I.bind (fun _ => nestedTensorPower J branches depth)).branchOperator
              outcome A
          else 0) =
      ∑ localOutcome : Xi,
        if secondPredicate localOutcome then
          J.branchOperator localOutcome
            (nestedTensorCoordinateOperator K branches depth path
              (∑ firstOutcome : Omega,
                if firstPredicate firstOutcome then
                  I.branchOperator firstOutcome A
                else 0))
        else 0 := by
  rw [bind_branchOperator_filter_sum_eq
    I (fun _ => nestedTensorPower J branches depth)
    firstPredicate
    (fun _ history => secondPredicate
      (nestedTensorHistoryAt Xi branches depth history path)) A]
  calc
    nestedTensorCoordinateOperator L branches depth path
        (∑ firstOutcome : Omega,
          if firstPredicate firstOutcome then
            ∑ history : nestedTensorHistory Xi branches depth,
              if secondPredicate
                  (nestedTensorHistoryAt Xi branches depth history path) then
                (nestedTensorPower J branches depth).branchOperator history
                  (I.branchOperator firstOutcome A)
              else 0
          else 0) =
      ∑ firstOutcome : Omega,
        if firstPredicate firstOutcome then
          ∑ localOutcome : Xi,
            if secondPredicate localOutcome then
              J.branchOperator localOutcome
                (nestedTensorCoordinateOperator K branches depth path
                  (I.branchOperator firstOutcome A))
            else 0
        else 0 := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro firstOutcome _
      by_cases hfirst : firstPredicate firstOutcome
      · rw [if_pos hfirst, if_pos hfirst]
        exact nestedTensor_coordinateOperator_branchOperator_filter_sum_eq
          J hJ secondPredicate branches depth
          (I.branchOperator firstOutcome A) path
      · simp [hfirst]
    _ = ∑ localOutcome : Xi,
        if secondPredicate localOutcome then
          J.branchOperator localOutcome
            (nestedTensorCoordinateOperator K branches depth path
              (∑ firstOutcome : Omega,
                if firstPredicate firstOutcome then
                  I.branchOperator firstOutcome A
                else 0))
        else 0 := by
      calc
        _ = ∑ firstOutcome : Omega,
            ∑ localOutcome : Xi,
              if firstPredicate firstOutcome ∧
                  secondPredicate localOutcome then
                J.branchOperator localOutcome
                  (nestedTensorCoordinateOperator K branches depth path
                    (I.branchOperator firstOutcome A))
              else 0 := by
            apply Finset.sum_congr rfl
            intro firstOutcome _
            by_cases hfirst : firstPredicate firstOutcome
            · simp [hfirst]
            · simp [hfirst]
        _ = ∑ localOutcome : Xi,
            ∑ firstOutcome : Omega,
              if firstPredicate firstOutcome ∧
                  secondPredicate localOutcome then
                J.branchOperator localOutcome
                  (nestedTensorCoordinateOperator K branches depth path
                    (I.branchOperator firstOutcome A))
              else 0 := by
            rw [Finset.sum_comm]
        _ = _ := by
            apply Finset.sum_congr rfl
            intro localOutcome _
            by_cases hlocal : secondPredicate localOutcome
            · simp only [hlocal, and_true]
              rw [map_sum, branchOperator_sum]
              apply Finset.sum_congr rfl
              intro firstOutcome _
              by_cases hfirst : firstPredicate firstOutcome
              · simp [hfirst]
              · simp [hfirst]
            · simp [hlocal]

/-- Named-operator form of the sequential selected-coordinate identity.  This
keeps downstream concrete protocols from unfolding and comparing the complete
dependent history enumeration merely to instantiate the source-neutral law. -/
theorem bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L) (hJ : J.kraus.Complete)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (path : nestedTensorPath branches depth)
    (A : Operator H) :
    bindNestedFilteredCoordinateOperator branches depth I J
        firstPredicate secondPredicate path A =
      filteredBranchOperatorSum J secondPredicate
        (nestedFilteredPredecessorCoordinateOperator branches depth I
          firstPredicate path A) := by
  exact bind_nestedTensor_coordinateOperator_branchOperator_filter_sum_eq
    branches depth I J hJ firstPredicate secondPredicate path A

/-- The real trace of one selected sequential nested event is its literal
finite Born-mass sum.  Retaining the selected output coordinate does not
change the trace because that marginal map is a quantum channel. -/
theorem bindNestedFilteredCoordinateOperator_trace_re_eq_bornWeight_sum
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (path : nestedTensorPath branches depth)
    (rho : DensityOperator H) :
    Complex.re (LinearMap.trace Complex L
      (bindNestedFilteredCoordinateOperator branches depth I J
        firstPredicate secondPredicate path rho.toOperator)) =
      ∑ outcome : Sigma fun _ : Omega =>
          nestedTensorHistory Xi branches depth,
        if firstPredicate outcome.1 ∧
            secondPredicate
              (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
          (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
            outcome rho
        else 0 := by
  classical
  unfold bindNestedFilteredCoordinateOperator
  rw [(nestedTensorCoordinateOperator L branches depth path).trace_map,
    map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases hevent : firstPredicate outcome.1 ∧
      secondPredicate
        (nestedTensorHistoryAt Xi branches depth outcome.2 path)
  · simp [hevent, bornWeight]
  · simp [hevent]

/-- A source-neutral union bound for a filtered predecessor event followed by
a nested stage.  Each possible failing leaf is charged to the real trace of
its local filtered branch on the true unnormalized predecessor marginal.
No branch is normalized and no product or sibling-independence premise is
used. -/
theorem
    bind_nestedTensor_bornWeight_first_and_any_path_failure_le_filteredBranchTrace
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L) (hJ : J.kraus.Complete)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (rho : DensityOperator H) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth =>
          firstPredicate outcome.1 ∧
            ∃ path : nestedTensorPath branches depth,
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)),
      (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
        outcome rho) <=
      ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (filteredBranchOperatorSum J secondPredicate
            (nestedFilteredPredecessorCoordinateOperator branches depth I
              firstPredicate path rho.toOperator))) := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ outcome : Sigma fun _ : Omega =>
          nestedTensorHistory Xi branches depth,
        if firstPredicate outcome.1 ∧
            (∃ path : nestedTensorPath branches depth,
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)) then
          (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
            outcome rho
        else 0) <=
        ∑ outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth,
          ∑ path : nestedTensorPath branches depth,
            if firstPredicate outcome.1 ∧
                secondPredicate
                  (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
              (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
                outcome rho
            else 0 := by
      apply Finset.sum_le_sum
      intro outcome _
      by_cases hfailure : firstPredicate outcome.1 ∧
          ∃ path : nestedTensorPath branches depth,
            secondPredicate
              (nestedTensorHistoryAt Xi branches depth outcome.2 path)
      · rw [if_pos hfailure]
        obtain ⟨hfirst, path, hpath⟩ := hfailure
        simpa [hfirst, hpath] using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset
              (nestedTensorPath branches depth)))
            (f := fun other : nestedTensorPath branches depth =>
              if firstPredicate outcome.1 ∧
                  secondPredicate
                    (nestedTensorHistoryAt Xi branches depth outcome.2 other) then
                (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
                  outcome rho
              else 0)
            (fun other _ => by
              by_cases hother : firstPredicate outcome.1 ∧
                  secondPredicate
                    (nestedTensorHistoryAt Xi branches depth outcome.2 other)
              · simpa [hother] using
                  (I.bind
                    (fun _ => nestedTensorPower J branches depth)).bornWeight_nonneg
                      outcome rho
              · simp [hother])
            (Finset.mem_univ path))
      · rw [if_neg hfailure]
        exact Finset.sum_nonneg fun path _ => by
          by_cases hpath : firstPredicate outcome.1 ∧
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)
          · simpa [hpath] using
              (I.bind
                (fun _ => nestedTensorPower J branches depth)).bornWeight_nonneg
                  outcome rho
          · simp [hpath]
    _ = ∑ path : nestedTensorPath branches depth,
        ∑ outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth,
          if firstPredicate outcome.1 ∧
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
            (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
              outcome rho
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (bindNestedFilteredCoordinateOperator branches depth I J
            firstPredicate secondPredicate path rho.toOperator)) := by
      apply Finset.sum_congr rfl
      intro path _
      exact
        (bindNestedFilteredCoordinateOperator_trace_re_eq_bornWeight_sum
          branches depth I J firstPredicate secondPredicate path rho).symm
    _ = ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (filteredBranchOperatorSum J secondPredicate
            (nestedFilteredPredecessorCoordinateOperator branches depth I
              firstPredicate path rho.toOperator))) := by
      apply Finset.sum_congr rfl
      intro path _
      rw [bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
        branches depth I J hJ firstPredicate secondPredicate path rho.toOperator]

/-- Implication-aware form of the same union bound.  A global predecessor
event may be stronger than the selected predecessor-path event; it suffices
to prove that the global event implies the selected event at every charged
path. -/
theorem
    bind_nestedTensor_bornWeight_first_implies_path_and_any_failure_le_filteredBranchTrace
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L) (hJ : J.kraus.Complete)
    (globalPredicate : Omega -> Prop) [DecidablePred globalPredicate]
    (pathPredicate : nestedTensorPath branches depth -> Omega -> Prop)
    [∀ path, DecidablePred (pathPredicate path)]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (hglobal : ∀ outcome path,
      globalPredicate outcome -> pathPredicate path outcome)
    (rho : DensityOperator H) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth =>
          globalPredicate outcome.1 ∧
            ∃ path : nestedTensorPath branches depth,
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)),
      (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
        outcome rho) <=
      ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (filteredBranchOperatorSum J secondPredicate
            (nestedFilteredPredecessorCoordinateOperator branches depth I
              (pathPredicate path) path rho.toOperator))) := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ outcome : Sigma fun _ : Omega =>
          nestedTensorHistory Xi branches depth,
        if globalPredicate outcome.1 ∧
            (∃ path : nestedTensorPath branches depth,
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)) then
          (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
            outcome rho
        else 0) <=
        ∑ outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth,
          ∑ path : nestedTensorPath branches depth,
            if pathPredicate path outcome.1 ∧
                secondPredicate
                  (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
              (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
                outcome rho
            else 0 := by
      apply Finset.sum_le_sum
      intro outcome _
      by_cases hfailure : globalPredicate outcome.1 ∧
          ∃ path : nestedTensorPath branches depth,
            secondPredicate
              (nestedTensorHistoryAt Xi branches depth outcome.2 path)
      · rw [if_pos hfailure]
        obtain ⟨hfirst, path, hpath⟩ := hfailure
        have hselected : pathPredicate path outcome.1 :=
          hglobal outcome.1 path hfirst
        simpa [hselected, hpath] using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset
              (nestedTensorPath branches depth)))
            (f := fun other : nestedTensorPath branches depth =>
              if pathPredicate other outcome.1 ∧
                  secondPredicate
                    (nestedTensorHistoryAt Xi branches depth outcome.2 other) then
                (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
                  outcome rho
              else 0)
            (fun other _ => by
              by_cases hother : pathPredicate other outcome.1 ∧
                  secondPredicate
                    (nestedTensorHistoryAt Xi branches depth outcome.2 other)
              · simpa [hother] using
                  (I.bind
                    (fun _ => nestedTensorPower J branches depth)).bornWeight_nonneg
                      outcome rho
              · simp [hother])
            (Finset.mem_univ path))
      · rw [if_neg hfailure]
        exact Finset.sum_nonneg fun path _ => by
          by_cases hpath : pathPredicate path outcome.1 ∧
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)
          · simpa [hpath] using
              (I.bind
                (fun _ => nestedTensorPower J branches depth)).bornWeight_nonneg
                  outcome rho
          · simp [hpath]
    _ = ∑ path : nestedTensorPath branches depth,
        ∑ outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth,
          if pathPredicate path outcome.1 ∧
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
            (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
              outcome rho
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (bindNestedFilteredCoordinateOperator branches depth I J
            (pathPredicate path) secondPredicate path rho.toOperator)) := by
      apply Finset.sum_congr rfl
      intro path _
      exact
        (bindNestedFilteredCoordinateOperator_trace_re_eq_bornWeight_sum
          branches depth I J (pathPredicate path) secondPredicate path rho).symm
    _ = ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (filteredBranchOperatorSum J secondPredicate
            (nestedFilteredPredecessorCoordinateOperator branches depth I
              (pathPredicate path) path rho.toOperator))) := by
      apply Finset.sum_congr rfl
      intro path _
      rw [bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
        branches depth I J hJ (pathPredicate path) secondPredicate path
          rho.toOperator]

end FiniteInstrument

end
end Semantics
end QEC
