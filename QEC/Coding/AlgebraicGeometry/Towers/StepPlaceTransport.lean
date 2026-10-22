import QEC.Coding.AlgebraicGeometry.Towers.Recursion
import QEC.Coding.AlgebraicGeometry.Towers.StepTransport

/-!
# Transporting simple-pole places into a Garcia--Stichtenoth successor

An algebraic equivalence transports a normalized global place by composing
its valuation with the equivalence.  Applying this to the identical step-field
presentations constructs an actual place of the recursively chosen successor
above any lower place where the current distinguished coordinate has a simple
pole.  The transported successor coordinate again has a simple pole.

No assertion is made here that these are all ramified places, nor is any
different, divisor, genus, or asymptotic conclusion packaged in the data.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

namespace GlobalPlace

variable {k K L : Type*} [Field k] [Finite k]
variable [Field K] [Algebra k K] [Field L] [Algebra k L]

/-- Pull a normalized global place back through an algebraic equivalence. -/
noncomputable def comapAlgEquiv (e : K ≃ₐ[k] L)
    (P : GlobalPlace k L) : GlobalPlace k K where
  valuation := P.valuation.comap e.toRingHom
  normalized := by
    intro gamma
    obtain ⟨y, hy⟩ := P.normalized gamma
    refine ⟨e.symm y, ?_⟩
    change P.valuation (e (e.symm y)) = gamma
    rw [e.apply_symm_apply, hy]

@[simp]
theorem comapAlgEquiv_order (e : K ≃ₐ[k] L)
    (P : GlobalPlace k L) (x : K) :
    (comapAlgEquiv e P).order x = P.order (e x) :=
  rfl

end GlobalPlace

namespace F256GarciaStichtenoth

/-- The actual place in recursive level `i+1` obtained from a simple-pole
place of the distinguished coordinate in level `i`. -/
noncomputable def transportedStepAbovePlace (i : ℕ)
    (P : GlobalPlace F256 (Field i))
    (hP : P.order (distinguishedCoordinate i) = -1) :
    GlobalPlace F256 (Field (i + 1)) :=
  GlobalPlace.comapAlgEquiv
    ((stepFieldEquiv (distinguishedPlace i) P
      (distinguishedCoordinate i) (distinguishedCoordinate_order i) hP).restrictScalars F256)
    (stepAbovePlace P (distinguishedCoordinate i) hP)

/-- The transported upper place makes the next distinguished coordinate a
normalized simple pole. -/
theorem transportedStepAbovePlace_order_distinguishedCoordinate
    (i : ℕ) (P : GlobalPlace F256 (Field i))
    (hP : P.order (distinguishedCoordinate i) = -1) :
    (transportedStepAbovePlace i P hP).order
        (distinguishedCoordinate (i + 1)) = -1 := by
  erw [transportedStepAbovePlace, GlobalPlace.comapAlgEquiv_order]
  change
    (stepAbovePlace P (distinguishedCoordinate i) hP).order
      (stepFieldEquiv (distinguishedPlace i) P
        (distinguishedCoordinate i) (distinguishedCoordinate_order i) hP
        (stepDistinguishedCoordinate (distinguishedPlace i)
          (distinguishedCoordinate i) (distinguishedCoordinate_order i))) = -1
  rw [stepFieldEquiv_stepDistinguishedCoordinate,
    stepAbovePlace_order_stepDistinguishedCoordinate]

end F256GarciaStichtenoth

end


end QEC.Coding.AlgebraicGeometry
