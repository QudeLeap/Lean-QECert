import QEC.Coding.FiniteFieldMultiplication.MultiplicationEmbedding
import QEC.Coding.FiniteFieldMultiplication.ReverseEmbedding

namespace QEC.Coding

/-- The binary functional obtained by applying the concrete RMFE projection after MFE reconstruction. -/
noncomputable def f256SelectorFunctional : (Fin 512 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  f256RMFEpsi.comp f256MFEPsi

/-- The coefficient of the concrete functional at one coordinate unit vector. -/
noncomputable def f256SelectorCoefficient (q : Fin 512) : ZMod 2 :=
  f256SelectorFunctional (Pi.single q 1)

/-- The finite coordinates whose concrete functional coefficient is one. -/
noncomputable def f256SelectedCoordinates : Finset (Fin 512) :=
  Finset.univ.filter fun q => f256SelectorCoefficient q = 1

/-- The explicit triple-zero coordinate of the length-512 MFE carrier. -/
noncomputable def f256SelectorQ0 : Fin 512 := f256MFEIndex 0 0 0

/-- Evaluation of the composed binary functional. -/
theorem f256SelectorFunctional_apply (v : Fin 512 → ZMod 2) :
    f256SelectorFunctional v = f256RMFEpsi (f256MFEPsi v) := rfl

private theorem f256SelectorQ0_eq_index_iff (i j k : Fin 8) :
    f256SelectorQ0 = f256MFEIndex i j k ↔ i = 0 ∧ j = 0 ∧ k = 0 := by
  constructor
  · intro h
    have hindex : (0, (0, 0)) = (i, (j, k)) := f256MFEIndexEquiv.injective (by
      simpa [f256SelectorQ0, f256MFEIndex] using h)
    have hi : (0 : Fin 8) = i := congrArg Prod.fst hindex
    have hjk : (0, 0) = (j, k) := congrArg Prod.snd hindex
    have hj : (0 : Fin 8) = j := congrArg Prod.fst hjk
    have hk : (0 : Fin 8) = k := congrArg Prod.snd hjk
    exact ⟨hi.symm, hj.symm, hk.symm⟩
  · rintro ⟨hi, hj, hk⟩
    subst i
    subst j
    subst k
    rfl

private theorem f256MFEIndex_eq_selectorQ0_iff (i j k : Fin 8) :
    f256MFEIndex i j k = f256SelectorQ0 ↔ i = 0 ∧ j = 0 ∧ k = 0 := by
  constructor
  · intro h
    exact (f256SelectorQ0_eq_index_iff i j k).mp h.symm
  · intro h
    exact ((f256SelectorQ0_eq_index_iff i j k).mpr h).symm

/-- MFE reconstruction sends the explicit coordinate unit vector to the field unit. -/
theorem f256MFEPsi_single_q0 :
    f256MFEPsi (Pi.single f256SelectorQ0 1) = 1 := by
  rw [f256MFEPsi_apply]
  classical
  simp [Pi.single_apply, f256MFEIndex_eq_selectorQ0_iff, f256PolynomialBasis_apply]
  rw [Fintype.sum_eq_single (0 : Fin 8)]
  · rw [Fintype.sum_eq_single (0 : Fin 8)]
    · rw [Fintype.sum_eq_single (0 : Fin 8)]
      · simp
      · intro k hk
        simp [hk]
    · intro j hj
      simp [hj]
  · intro i hi
    simp [hi]

/-- The concrete RMFE projection maps the field unit to the binary unit. -/
theorem f256RMFEpsi_one : f256RMFEpsi 1 = 1 := by
  simpa [f256RMFEphi_apply] using f256RMFEpsi_phi (1 : ZMod 2)

/-- The explicit coordinate has coefficient one under the composed functional. -/
theorem f256SelectorCoefficient_q0 : f256SelectorCoefficient f256SelectorQ0 = 1 := by
  rw [f256SelectorCoefficient, f256SelectorFunctional_apply, f256MFEPsi_single_q0]
  exact f256RMFEpsi_one

/-- The explicit coordinate belongs to the actual filtered coordinate collection. -/
theorem f256SelectorQ0_mem_selectedCoordinates :
    f256SelectorQ0 ∈ f256SelectedCoordinates := by
  simp [f256SelectedCoordinates, f256SelectorCoefficient_q0]

/-- The actual filtered coordinate collection is nonempty. -/
theorem f256SelectedCoordinates_nonempty : f256SelectedCoordinates.Nonempty :=
  ⟨f256SelectorQ0, f256SelectorQ0_mem_selectedCoordinates⟩

/-- The actual filtered coordinate collection has positive cardinality. -/
theorem f256SelectedCoordinates_card_pos : 0 < f256SelectedCoordinates.card :=
  Finset.card_pos.mpr f256SelectedCoordinates_nonempty

/-- The actual filtered coordinate collection contains at least one coordinate. -/
theorem f256SelectedCoordinates_card_ge_one : 1 ≤ f256SelectedCoordinates.card :=
  Nat.succ_le_iff.mpr f256SelectedCoordinates_card_pos

/-- The fraction of one length-512 MFE block occupied by selected coordinates. -/
noncomputable def f256SelectedCoordinateFraction : ℚ :=
  (f256SelectedCoordinates.card : ℚ) / 512

/-- The explicit selected coordinate gives the normalized lower bound `1/512`. -/
theorem f256SelectedCoordinateFraction_lower_bound :
    (1 : ℚ) / 512 ≤ f256SelectedCoordinateFraction := by
  rw [f256SelectedCoordinateFraction]
  have hcard : (1 : ℚ) ≤ f256SelectedCoordinates.card := by
    exact_mod_cast f256SelectedCoordinates_card_ge_one
  nlinarith

end QEC.Coding
