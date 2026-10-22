import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Arithmetic.StrongApproximation

/-!
# Global norm-one comparison for the Cartwright--Steger inner form

This module connects the split-coordinate arithmetic norm-one group back to
the reduced-norm-one subgroup of the original cyclic division algebra.  It
also records that the explicit generator-ratio witness belongs to the global
and building-place reduced-norm kernels simultaneously, without assuming
that the two determinant definitions agree on every unit.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- The explicit ratio, bundled in the global reduced-norm-one group. -/
noncomputable def cyclicAlgebraSplitNormOneGeneratorRatio
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    CyclicAlgebraSplitNormOne P r :=
  ⟨cyclicAlgebraBuildingNormOneGeneratorRatio P r u v,
    cyclicAlgebraBuildingNormOneGeneratorRatio_mem_splitNormOne P r u v⟩

@[simp] theorem cyclicAlgebraSplitNormOneGeneratorRatio_val
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    (cyclicAlgebraSplitNormOneGeneratorRatio P r u v :
        (CyclicAlgebra P r)ˣ) =
      (cyclicAlgebraBuildingNormOneGeneratorRatio P r u v :
        (CyclicAlgebra P r)ˣ) :=
  rfl

theorem cyclicAlgebraSplitNormOneGeneratorRatio_ne_one
    (P : BasePrime) (r : Rank)
    {u v : ConstantProjectiveClass P r} (huv : u ≠ v) :
    cyclicAlgebraSplitNormOneGeneratorRatio P r u v ≠ 1 := by
  intro hratio
  apply cyclicAlgebraBuildingNormOneGeneratorRatio_ne_one P r huv
  have hval :
      (cyclicAlgebraSplitNormOneGeneratorRatio P r u v :
          (CyclicAlgebra P r)ˣ) = 1 :=
    congrArg Subtype.val hratio
  apply Subtype.ext
  exact hval

theorem exists_ne_one_cyclicAlgebraSplitNormOne
    (P : BasePrime) (r : Rank) :
    ∃ g : CyclicAlgebraSplitNormOne P r, g ≠ 1 := by
  letI : Nontrivial (ConstantProjectiveClass P r) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa [Nat.card_eq_fintype_card] using
        one_lt_natCard_constantProjectiveClass P r)
  obtain ⟨u, v, huv⟩ := exists_pair_ne (ConstantProjectiveClass P r)
  exact ⟨cyclicAlgebraSplitNormOneGeneratorRatio P r u v,
    cyclicAlgebraSplitNormOneGeneratorRatio_ne_one P r huv⟩

/-- The split-coordinate norm-one inner form maps all the way back to the
global reduced-norm-one subgroup of the original cyclic division algebra. -/
noncomputable def orderNormOneInnerFormToCyclicAlgebraSplitNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      CyclicAlgebraSplitNormOne P r :=
  (orderNormOneToCyclicAlgebraNormOne P r).comp
    (orderNormOneInnerFormToActualNormOne P r)

theorem orderNormOneInnerFormToCyclicAlgebraSplitNormOne_val
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    (orderNormOneInnerFormToCyclicAlgebraSplitNormOne P r s :
        (CyclicAlgebra P r)ˣ) =
      orderUnitToCyclicUnit P r
        (orderNormOneInnerFormToOrderUnits P r s) :=
  rfl

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
