import QEC.Semantics.Instruments.TensorPower.BornMass
/-!
# Finite tensor-power rejection counts and first moments

This internal API counts rejections directly from finite observed histories.
It is the deterministic counting layer used by the later Born-weighted
first-moment argument and derives all quantities from those histories.
-/

universe u v w

namespace QEC
namespace Semantics

open scoped BigOperators

noncomputable section

namespace FiniteInstrument

/-- The number of finite trials whose actual observed history does not satisfy
the supplied acceptance predicate. -/
def tensorPowerRejectedCount {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts : Nat)
    (history : tensorPowerHistory Ω attempts) : Nat :=
  attempts - (tensorPowerAcceptedIndices accepts attempts history).card

/-- The actual accepted and rejected trial counts partition the finite retry
history. -/
theorem tensorPowerAcceptedCount_add_rejectedCount {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts : Nat)
    (history : tensorPowerHistory Ω attempts) :
    (tensorPowerAcceptedIndices accepts attempts history).card +
      tensorPowerRejectedCount accepts attempts history = attempts := by
  unfold tensorPowerRejectedCount
  have hcard : (tensorPowerAcceptedIndices accepts attempts history).card ≤ attempts := by
    calc
      (tensorPowerAcceptedIndices accepts attempts history).card ≤
          (Finset.univ : Finset (Fin attempts)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = attempts := by simp
  omega

/-- A history short of `required` accepted trials has at least
`attempts - required + 1` actual rejections. -/
theorem tensorPowerShortage_rejectedCount_lower_bound {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (history : tensorPowerHistory Ω attempts) (hrequired : required ≤ attempts)
    (hshort : (tensorPowerAcceptedIndices accepts attempts history).card < required) :
    attempts - required + 1 ≤ tensorPowerRejectedCount accepts attempts history := by
  unfold tensorPowerRejectedCount
  omega

/-- Accepted-index cardinalities recurse over the actual right-nested finite
history. -/
theorem tensorPowerAcceptedIndices_card_succ {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts : Nat)
    (head : Ω) (tail : tensorPowerHistory Ω attempts) :
    (tensorPowerAcceptedIndices accepts (attempts + 1) (head, tail)).card =
      (if accepts head then 1 else 0) +
        (tensorPowerAcceptedIndices accepts attempts tail).card := by
  unfold tensorPowerAcceptedIndices
  rw [Fin.card_filter_univ_succ']
  simp [tensorPowerHistoryAt]
  rfl

/-- The finite rejection count adds exactly the new non-accepted outcome at a
successor trial. -/
theorem tensorPowerRejectedCount_succ {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts : Nat)
    (head : Ω) (tail : tensorPowerHistory Ω attempts) :
    tensorPowerRejectedCount accepts (attempts + 1) (head, tail) =
      (if accepts head then 0 else 1) +
        tensorPowerRejectedCount accepts attempts tail := by
  have htail : (tensorPowerAcceptedIndices accepts attempts tail).card ≤ attempts := by
    calc
      (tensorPowerAcceptedIndices accepts attempts tail).card ≤
          (Finset.univ : Finset (Fin attempts)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = attempts := by simp
  unfold tensorPowerRejectedCount
  rw [tensorPowerAcceptedIndices_card_succ]
  by_cases hhead : accepts head <;> simp [hhead] <;> omega

/-- The actual finite Born-weighted rejected count over tensor-power histories
of a finite-outcome instrument. -/
noncomputable def tensorPowerRejectedFirstMoment
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (rho : DensityOperator H)
    (_rhoUnit : DensityOperator (tensorPowerCarrier H 0)) (attempts : Nat) : ℝ :=
  ∑ history : tensorPowerHistory Ω attempts,
    (tensorPowerRejectedCount accepts attempts history : ℝ) *
      tensorPowerBornProduct I rho attempts history

/-- Completeness normalizes the total recursively factored observed Born mass
of every finite tensor-power history. -/
private theorem tensorPowerBornProduct_sum_eq_one
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (hI : I.kraus.Complete)
    (rho : DensityOperator H) :
    ∀ attempts : Nat,
      ∑ history : tensorPowerHistory Ω attempts,
        tensorPowerBornProduct I rho attempts history = 1
  | 0 => by
      change (∑ _ : PUnit, (1 : ℝ)) = 1
      simp
  | attempts + 1 => by
      change (∑ history : Ω × tensorPowerHistory Ω attempts,
        I.bornWeight history.1 rho * tensorPowerBornProduct I rho attempts history.2) = 1
      rw [Fintype.sum_prod_type]
      calc
        _ = (∑ head : Ω, I.bornWeight head rho) *
            ∑ tail : tensorPowerHistory Ω attempts,
              tensorPowerBornProduct I rho attempts tail := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro head _
          rw [Finset.mul_sum]
        _ = 1 := by
          rw [I.sum_bornWeight_eq_one hI rho,
            tensorPowerBornProduct_sum_eq_one I hI rho attempts]
          norm_num

/-- Actual tensor-power rejection first moments are the number of trials times
the one-block Born mass of the actual non-accepted outcomes. -/
theorem tensorPowerRejectedFirstMoment_eq_attempts_mul_rejectedBornWeight
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (hI : I.kraus.Complete)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ attempts : Nat,
      tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts =
        (attempts : ℝ) *
          ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
            I.bornWeight outcome rho
  | 0 => by
      simp [tensorPowerRejectedFirstMoment, tensorPowerRejectedCount,
        tensorPowerAcceptedIndices, tensorPowerBornProduct]
  | attempts + 1 => by
      have htotal := tensorPowerBornProduct_sum_eq_one I hI rho attempts
      have hind := tensorPowerRejectedFirstMoment_eq_attempts_mul_rejectedBornWeight
        I accepts hI rho rhoUnit attempts
      have hborn :
          (∑ outcome ∈ Finset.univ.filter accepts, I.bornWeight outcome rho) +
            (∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
              I.bornWeight outcome rho) = 1 := by
        calc
          _ = ∑ outcome : Ω, I.bornWeight outcome rho := by
            simpa using Finset.sum_filter_add_sum_filter_not
              (s := (Finset.univ : Finset Ω)) (p := accepts)
              (f := fun outcome => I.bornWeight outcome rho)
          _ = 1 := I.sum_bornWeight_eq_one hI rho
      change
        (∑ history : Ω × tensorPowerHistory Ω attempts,
          (tensorPowerRejectedCount accepts (attempts + 1) history : ℝ) *
            (I.bornWeight history.1 rho * tensorPowerBornProduct I rho attempts history.2)) =
          ((attempts + 1 : Nat) : ℝ) *
            ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
              I.bornWeight outcome rho
      rw [Fintype.sum_prod_type]
      rw [← Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset Ω)) (p := accepts)
        (f := fun head => ∑ tail : tensorPowerHistory Ω attempts,
          (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
            (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail))]
      have haccept (head : Ω) (hhead : accepts head) :
          (∑ tail : tensorPowerHistory Ω attempts,
            (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
              (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail)) =
            I.bornWeight head rho *
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts := by
        unfold tensorPowerRejectedFirstMoment
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro tail _
        rw [tensorPowerRejectedCount_succ]
        simp [hhead]
        ring
      have hreject (head : Ω) (hhead : ¬ accepts head) :
          (∑ tail : tensorPowerHistory Ω attempts,
            (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
              (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail)) =
            I.bornWeight head rho *
              ((∑ tail : tensorPowerHistory Ω attempts,
                tensorPowerBornProduct I rho attempts tail) +
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts) := by
        unfold tensorPowerRejectedFirstMoment
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro tail _
        rw [tensorPowerRejectedCount_succ]
        simp [hhead]
        ring
      have hsumAccept :
          (∑ head ∈ Finset.univ.filter accepts,
            ∑ tail : tensorPowerHistory Ω attempts,
              (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
                (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail)) =
            (∑ head ∈ Finset.univ.filter accepts, I.bornWeight head rho) *
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro head hhead
        exact haccept head (Finset.mem_filter.mp hhead).2
      have hsumReject :
          (∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
            ∑ tail : tensorPowerHistory Ω attempts,
              (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
                (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail)) =
            (∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho) *
              ((∑ tail : tensorPowerHistory Ω attempts,
                tensorPowerBornProduct I rho attempts tail) +
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro head hhead
        exact hreject head (Finset.mem_filter.mp hhead).2
      rw [hsumAccept, hsumReject]
      calc
        _ = ((∑ head ∈ Finset.univ.filter accepts, I.bornWeight head rho) +
              ∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
                I.bornWeight head rho) *
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts +
            (∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho) *
              ∑ tail : tensorPowerHistory Ω attempts,
                tensorPowerBornProduct I rho attempts tail := by
          ring
        _ = tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts +
            ∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho := by
          rw [hborn, htotal]
          ring
        _ = (attempts : ℝ) *
              (∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
                I.bornWeight head rho) +
            ∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho := by
          rw [hind]
        _ = ((attempts + 1 : Nat) : ℝ) *
            ∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho := by
          push_cast
          ring

/-- A finite shortage event has Markov mass bounded by the actual rejected
first moment on the recursively tensorized product input. -/
theorem tensorPowerShortageMass_markov_le_rejectedBornWeight
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (hI : I.kraus.Complete) (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (attempts required : Nat) (hrequired : required ≤ attempts) :
    ((attempts - required + 1 : Nat) : ℝ) *
        I.tensorPowerShortageMass accepts attempts required
          (tensorPowerProductInput rho rhoUnit attempts) ≤
      (attempts : ℝ) *
        ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
          I.bornWeight outcome rho := by
  let productInput := tensorPowerProductInput rho rhoUnit attempts
  calc
    _ = ∑ history ∈ Finset.univ.filter
        (fun history =>
          (tensorPowerAcceptedIndices accepts attempts history).card < required),
        ((attempts - required + 1 : Nat) : ℝ) *
          (I.tensorPower attempts).bornWeight history productInput := by
      unfold tensorPowerShortageMass
      rw [Finset.mul_sum]
    _ ≤ ∑ history ∈ Finset.univ.filter
        (fun history =>
          (tensorPowerAcceptedIndices accepts attempts history).card < required),
        (tensorPowerRejectedCount accepts attempts history : ℝ) *
          (I.tensorPower attempts).bornWeight history productInput := by
      apply Finset.sum_le_sum
      intro history hhistory
      have hshort := (Finset.mem_filter.mp hhistory).2
      have hcount : ((attempts - required + 1 : Nat) : ℝ) ≤
          (tensorPowerRejectedCount accepts attempts history : ℝ) := by
        exact_mod_cast tensorPowerShortage_rejectedCount_lower_bound accepts attempts required
          history hrequired hshort
      exact mul_le_mul_of_nonneg_right hcount
        ((I.tensorPower attempts).bornWeight_nonneg history productInput)
    _ ≤ ∑ history : tensorPowerHistory Ω attempts,
        (tensorPowerRejectedCount accepts attempts history : ℝ) *
          (I.tensorPower attempts).bornWeight history productInput := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro history _ _
      exact mul_nonneg (Nat.cast_nonneg _)
        ((I.tensorPower attempts).bornWeight_nonneg history productInput)
    _ = tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts := by
      unfold tensorPowerRejectedFirstMoment
      apply Finset.sum_congr rfl
      intro history _
      rw [bornWeight_tensorPower]
    _ = _ := tensorPowerRejectedFirstMoment_eq_attempts_mul_rejectedBornWeight
      I accepts hI rho rhoUnit attempts

end FiniteInstrument

end
end Semantics
end QEC
