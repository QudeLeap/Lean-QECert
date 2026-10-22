import QEC.Coding.AlgebraicGeometry.Codes.Evaluation

/-!
# The exact evaluation kernel

Vanishing at a set of rational coordinates is equivalent to subtracting
their reduced divisor. This gives the actual shortening identity used in
[Ngu24, Theorem: AG multiplication family], as well as the kernel dimension
needed for interpolation from Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped BigOperators

noncomputable section

variable {k F ι : Type*} [Field k] [Finite k] [Field F] [Algebra k F] [Fintype ι]

theorem zeroCoordinateDivisor_nonnegative (Q : ι → RationalPlace k F) (S : Finset ι) :
    0 ≤ zeroCoordinateDivisor Q S := by
  classical
  intro P
  change 0 ≤ zeroCoordinateDivisor Q S P
  unfold zeroCoordinateDivisor
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro j _
  simp only [Finsupp.single_apply]
  split_ifs <;> norm_num

/-- The converse to the valuation-bound implication in `Evaluation`. -/
theorem evaluationZeroOn_of_mem_riemannRochSubmodule_sub
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (S : Finset ι)
    (f : GlobalPlace.riemannRochSubmodule G)
    (hf : (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S)) :
    ∀ j ∈ S, agEvaluationLinearMap G Q hG f j = 0 := by
  intro j hj
  rw [agEvaluationLinearMap_apply, (Q j).evaluateRegular_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  change (Q j).place.valuation (f : F) < 1
  have hb := (GlobalPlace.mem_riemannRochSubmodule_iff _ _).mp hf (Q j).place
  rw [Finsupp.sub_apply, hG j, zeroCoordinateDivisor_apply_at Q hQ S hj] at hb
  apply lt_of_le_of_lt hb
  simpa only [WithZero.exp_zero] using
    (WithZero.exp_lt_exp.mpr (by norm_num : (0 : ℤ) - 1 < 0))

theorem evaluationZeroOn_iff_mem_riemannRochSubmodule_sub
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (S : Finset ι)
    (f : GlobalPlace.riemannRochSubmodule G) :
    (∀ j ∈ S, agEvaluationLinearMap G Q hG f j = 0) ↔
      (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S) :=
  ⟨evaluationZeroOn_mem_riemannRochSubmodule_sub G Q hQ hG S f,
    evaluationZeroOn_of_mem_riemannRochSubmodule_sub G Q hQ hG S f⟩

/-- The evaluation kernel is the smaller Riemann--Roch space, not an abstract
space chosen to have the same dimension. -/
def agEvaluationKernelEquiv
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) :
    (agEvaluationLinearMap G Q hG).ker ≃ₗ[k]
      GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) where
  toFun f := ⟨(f.val : F), evaluationZero_mem_riemannRochSubmodule_sub G Q hQ hG
    f.val (LinearMap.mem_ker.mp f.property)⟩
  invFun f := by
    let fG : GlobalPlace.riemannRochSubmodule G :=
      ⟨(f : F), GlobalPlace.riemannRochSubmodule_mono
        (sub_le_self G (zeroCoordinateDivisor_nonnegative Q Finset.univ)) f.property⟩
    refine ⟨fG, LinearMap.mem_ker.mpr ?_⟩
    ext j
    exact evaluationZeroOn_of_mem_riemannRochSubmodule_sub G Q hQ hG Finset.univ
      fG f.property j (Finset.mem_univ j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end QEC.Coding.AlgebraicGeometry
