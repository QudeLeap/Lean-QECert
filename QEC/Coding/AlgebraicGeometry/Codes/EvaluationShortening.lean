import QEC.Coding.AlgebraicGeometry.Codes.EvaluationKernel

/-!
# Shortening is evaluation for the subtracted divisor

The retained words are precisely the punctures of original codewords that
vanish at every removed coordinate. The theorem identifies these words with
the actual AG evaluation range for `G - D_removed`, as in the last paragraph
of [Ngu24, Theorem: AG multiplication family].
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

variable {k F ι J : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
variable [Fintype ι] [Fintype J]

theorem evaluationSupport_sub_of_not_range
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (p : J ↪ ι)
    (j : {j : ι // j ∉ Set.range p}) :
    (G - evaluationDivisor (fun a => Q (p a))) (Q j.val).place = 0 := by
  rw [Finsupp.sub_apply, hG j.val]
  have hz : evaluationDivisor (fun a => Q (p a)) (Q j.val).place = 0 := by
    apply zeroCoordinateDivisor_apply_eq_zero_of_not_mem
    intro a _ heq
    exact j.property ⟨a, hQ heq⟩
  rw [hz, sub_zero]

/-- A precise membership characterization of the AG shortened code. -/
theorem mem_agEvaluation_sub_divisor_iff_shortened
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (p : J ↪ ι)
    [Fintype {j : ι // j ∉ Set.range p}]
    (w : Word k {j : ι // j ∉ Set.range p}) :
    w ∈ (agEvaluationCode (G - evaluationDivisor (fun a => Q (p a)))
      (fun j : {j : ι // j ∉ Set.range p} => Q j.val)
      (evaluationSupport_sub_of_not_range G Q hQ hG p)).carrier ↔
    ∃ x ∈ (agEvaluationCode G Q hG).carrier,
      (∀ a, x (p a) = 0) ∧ (fun j : {j : ι // j ∉ Set.range p} => x j.val) = w := by
  have hQp : Function.Injective fun a => (Q (p a)).place := hQ.comp p.injective
  have hGp : ∀ a, G (Q (p a)).place = 0 := fun a => hG (p a)
  have hle : G - evaluationDivisor (fun a => Q (p a)) ≤ G :=
    sub_le_self G (zeroCoordinateDivisor_nonnegative (fun a => Q (p a)) Finset.univ)
  constructor
  · rintro ⟨f, rfl⟩
    let fG : GlobalPlace.riemannRochSubmodule G :=
      ⟨f, GlobalPlace.riemannRochSubmodule_mono hle f.property⟩
    refine ⟨agEvaluationLinearMap G Q hG fG, ⟨fG, rfl⟩, ?_, rfl⟩
    intro a
    exact evaluationZeroOn_of_mem_riemannRochSubmodule_sub G (fun a => Q (p a))
      hQp hGp Finset.univ fG f.property a (Finset.mem_univ a)
  · rintro ⟨x, ⟨f, rfl⟩, hzero, hword⟩
    have hf : (f : F) ∈ GlobalPlace.riemannRochSubmodule
        (G - evaluationDivisor (fun a => Q (p a))) := by
      apply evaluationZero_mem_riemannRochSubmodule_sub G (fun a => Q (p a)) hQp hGp f
      ext a
      exact hzero a
    exact ⟨⟨f, hf⟩, hword⟩

end

end QEC.Coding.AlgebraicGeometry
