import QEC.Semantics.Entropy.FiniteDimensional
import QEC.Semantics.ErrorCorrection.QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Finite spectral entropy dimension bounds

This module proves the finite-dimensional maximum-entropy bound directly from
the spectral probability data of a `DensityOperator`. The qudit corollaries
compute the dimension of the concrete selected register from its
computational-basis label type.
-/

universe u

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

noncomputable section

namespace DensityOperator

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

/-- The base-two entropy contribution is a positive rescaling of `negMulLog`. -/
theorem entropyTerm_eq_negMulLog_div_logTwo (x : Real) :
    entropyTerm x = (Real.log 2)⁻¹ * Real.negMulLog x := by
  by_cases hx : x = 0
  · subst x
    simp [entropyTerm, Real.negMulLog]
  · rw [entropyTerm, if_neg hx]
    simp only [Real.logb, Real.negMulLog]
    ring

/-- The base-two entropy contribution is concave on the nonnegative reals. -/
theorem entropyTerm_concaveOn_nonnegative :
    ConcaveOn Real (Set.Ici (0 : Real)) entropyTerm := by
  rw [show entropyTerm = fun x => (Real.log 2)⁻¹ • Real.negMulLog x from
    funext entropyTerm_eq_negMulLog_div_logTwo]
  exact Real.concaveOn_negMulLog.smul (by positivity)

/-- Finite Jensen for base-two entropy with uniform weights. -/
theorem entropyTerm_sum_le_card_mul_entropyTerm_reciprocal (n : Nat) (hn : 0 < n)
    (p : Fin n -> Real) (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (∑ i, entropyTerm (p i)) <= (n : Real) * entropyTerm ((n : Real)⁻¹) := by
  let w : Fin n -> Real := fun _ => (n : Real)⁻¹
  have hweights : (∑ i, w i) = 1 := by
    simp [w, hn.ne']
  have hmean : (∑ i, w i * p i) = (n : Real)⁻¹ := by
    calc
      ∑ i, w i * p i = (n : Real)⁻¹ * ∑ i, p i := by
        simp [w, Finset.mul_sum]
      _ = (n : Real)⁻¹ := by rw [hsum, mul_one]
  have hJensen := entropyTerm_concaveOn_nonnegative.le_map_sum
    (t := Finset.univ) (w := w) (p := p)
    (by intro i _; exact inv_nonneg.mpr (Nat.cast_nonneg n)) hweights
    (by intro i _; exact hp i)
  have hmean_smul : (∑ i, w i • p i) = (n : Real)⁻¹ := by
    simpa [smul_eq_mul] using hmean
  rw [hmean_smul] at hJensen
  calc
    (∑ i, entropyTerm (p i)) =
        (n : Real) * (∑ i, w i * entropyTerm (p i)) := by
      simp [w, Finset.mul_sum, hn.ne']
    _ <= (n : Real) * entropyTerm ((n : Real)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hJensen (Nat.cast_nonneg n)

/-- The uniform Jensen right-hand side is exactly the base-two logarithm of the cardinality. -/
theorem card_mul_entropyTerm_reciprocal_eq_logb (n : Nat) (hn : 0 < n) :
    (n : Real) * entropyTerm ((n : Real)⁻¹) = Real.logb 2 (n : Real) := by
  rw [entropyTerm, if_neg (inv_ne_zero (by exact_mod_cast hn.ne')), Real.logb_inv]
  field_simp

/-- A finite probability vector has entropy at most the logarithm of its cardinality. -/
theorem finite_jensen_entropyTerm_sum_le_logb_card (n : Nat) (hn : 0 < n)
    (p : Fin n -> Real) (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (∑ i, entropyTerm (p i)) <= Real.logb 2 (n : Real) := by
  calc
    (∑ i, entropyTerm (p i)) <= (n : Real) * entropyTerm ((n : Real)⁻¹) :=
      entropyTerm_sum_le_card_mul_entropyTerm_reciprocal n hn p hp hsum
    _ = Real.logb 2 (n : Real) := card_mul_entropyTerm_reciprocal_eq_logb n hn

/-- A density operator can only live on a nonzero finite-dimensional system. -/
theorem finrank_pos (rho : DensityOperator H) : 0 < Module.finrank Complex H := by
  by_contra h
  have hzero : Module.finrank Complex H = 0 := Nat.eq_zero_of_not_pos h
  letI : IsEmpty (Fin (Module.finrank Complex H)) := ⟨fun i => by
    exact (Nat.not_lt_zero i.1) (by simpa [hzero] using i.2)⟩
  have hsum := rho.spectralEigenvalues_sum_eq_one
  simp at hsum

/-- Spectral maximum entropy for every finite-dimensional density operator. -/
theorem vonNeumannEntropy_le_log_finrank (rho : DensityOperator H) :
    rho.vonNeumannEntropy <= Real.logb 2 (Module.finrank Complex H : Real) := by
  rw [rho.vonNeumannEntropy_eq_sum_spectralEigenvalues]
  exact finite_jensen_entropyTerm_sum_le_logb_card (Module.finrank Complex H) rho.finrank_pos
    rho.spectralEigenvalues (fun i => rho.spectralEigenvalues_nonnegative i)
    rho.spectralEigenvalues_sum_eq_one

end DensityOperator

namespace Qudit

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The dimension of a concrete finite-qudit register is the product of its
site-wise local dimensions. -/
theorem finrank_quditRegister_eq_prod_dimensions (q : ι -> Nat) :
    Module.finrank Complex (QuditRegister q) = ∏ i, q i := by
  rw [finrank_euclideanSpace]
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]

/-- Existence of a density operator on a concrete register forces every local
dimension in that register to be positive. -/
theorem dimensions_positive_of_density (q : ι -> Nat)
    (rho : DensityOperator (QuditRegister q)) :
    forall i, 0 < q i := by
  have hproduct : 0 < ∏ i, q i := by
    rw [← finrank_quditRegister_eq_prod_dimensions]
    exact rho.finrank_pos
  intro i
  exact Nat.pos_of_ne_zero ((Finset.prod_ne_zero_iff.mp (Nat.ne_of_gt hproduct)) i
    (Finset.mem_univ _))

/-- The base-two logarithm of a concrete register dimension is the sum of its
site-wise base-two logarithms. -/
theorem log_finrank_quditRegister_eq_sum_log_dimensions (q : ι -> Nat)
    (hq : forall i, 0 < q i) :
    Real.logb 2 (Module.finrank Complex (QuditRegister q) : Real) =
      ∑ i, Real.logb 2 (q i : Real) := by
  rw [finrank_quditRegister_eq_prod_dimensions]
  push_cast
  simpa using Real.logb_prod Finset.univ (fun i => (q i : Real)) (fun i _ => by
    change (q i : Real) ≠ 0
    exact_mod_cast Nat.ne_of_gt (hq i))

/-- Maximum entropy on a concrete finite-qudit register is bounded by its
heterogeneous local-dimension logarithm sum. -/
theorem vonNeumannEntropy_le_sum_log_registerDimensions (q : ι -> Nat)
    (rho : DensityOperator (QuditRegister q)) :
    rho.vonNeumannEntropy <= ∑ i, Real.logb 2 (q i : Real) := by
  calc
    rho.vonNeumannEntropy <= Real.logb 2 (Module.finrank Complex (QuditRegister q) : Real) :=
      rho.vonNeumannEntropy_le_log_finrank
    _ = ∑ i, Real.logb 2 (q i : Real) :=
      log_finrank_quditRegister_eq_sum_log_dimensions q
        (dimensions_positive_of_density q rho)

end Qudit

namespace QuditSubsystem

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι -> Nat}

/-- The selected register dimension is the product of its concrete local dimensions. -/
theorem finrank_selectedSystem_eq_prod_selectedDimensions (S : QuditSubsystem q) :
    Module.finrank Complex S.selectedSystem = ∏ i ∈ S.selected, q i := by
  rw [finrank_euclideanSpace]
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  change (∏ i : S.SelectedCoordinates, q i) = ∏ i ∈ S.selected, q i
  exact (Finset.prod_subtype S.selected (fun i => Iff.rfl) fun i => q i).symm

/-- Existence of a selected-system density operator forces all selected local dimensions positive. -/
theorem selectedDimensions_positive_of_density (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    forall i, i ∈ S.selected -> 0 < q i := by
  have hfinrank := DensityOperator.finrank_pos rho
  have hproduct : 0 < ∏ i ∈ S.selected, q i := by
    rw [← S.finrank_selectedSystem_eq_prod_selectedDimensions]
    exact hfinrank
  intro i hi
  exact Nat.pos_of_ne_zero ((Finset.prod_ne_zero_iff.mp (Nat.ne_of_gt hproduct)) i hi)

/-- The base-two logarithm of a concrete selected-register dimension is its local log sum. -/
theorem log_finrank_selectedSystem_eq_sum_log_selectedDimensions (S : QuditSubsystem q)
    (hq : forall i, i ∈ S.selected -> 0 < q i) :
    Real.logb 2 (Module.finrank Complex S.selectedSystem : Real) =
      ∑ i ∈ S.selected, Real.logb 2 (q i : Real) := by
  rw [S.finrank_selectedSystem_eq_prod_selectedDimensions]
  push_cast
  exact Real.logb_prod S.selected (fun i => (q i : Real)) (fun i hi => by
    change (q i : Real) ≠ 0
    exact_mod_cast Nat.ne_of_gt (hq i hi))

/-- Maximum entropy on a concrete selected qudit system is bounded by its heterogeneous log sum. -/
theorem vonNeumannEntropy_le_sum_log_selectedDimensions (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    rho.vonNeumannEntropy <= ∑ i ∈ S.selected, Real.logb 2 (q i : Real) := by
  calc
    rho.vonNeumannEntropy <= Real.logb 2 (Module.finrank Complex S.selectedSystem : Real) :=
      rho.vonNeumannEntropy_le_log_finrank
    _ = ∑ i ∈ S.selected, Real.logb 2 (q i : Real) :=
      S.log_finrank_selectedSystem_eq_sum_log_selectedDimensions
        (S.selectedDimensions_positive_of_density rho)

/-- A uniform local-dimension bound controls the selected-region heterogeneous log sum. -/
theorem sum_log_selectedDimensions_le_card_mul_log_uniformDimension (S : QuditSubsystem q)
    (hq : forall i, 0 < q i) (D : Nat)
    (hD : forall i, i ∈ S.selected -> q i <= D) :
    (∑ i ∈ S.selected, Real.logb 2 (q i : Real)) <=
      (S.selected.card : Real) * Real.logb 2 (D : Real) := by
  calc
    (∑ i ∈ S.selected, Real.logb 2 (q i : Real)) <=
        ∑ i ∈ S.selected, Real.logb 2 (D : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hq i)
        (by exact_mod_cast hD i hi)
    _ = (S.selected.card : Real) * Real.logb 2 (D : Real) := by
      simp [nsmul_eq_mul]

/-- Maximum entropy on a selected qudit region under an explicit uniform local bound. -/
theorem vonNeumannEntropy_le_card_mul_log_uniformDimension (S : QuditSubsystem q)
    (hq : forall i, 0 < q i) (D : Nat)
    (hD : forall i, i ∈ S.selected -> q i <= D) (rho : DensityOperator S.selectedSystem) :
    rho.vonNeumannEntropy <= (S.selected.card : Real) * Real.logb 2 (D : Real) := by
  exact (S.vonNeumannEntropy_le_sum_log_selectedDimensions rho).trans
    (S.sum_log_selectedDimensions_le_card_mul_log_uniformDimension hq D hD)

end QuditSubsystem

end
end Semantics
end QEC
