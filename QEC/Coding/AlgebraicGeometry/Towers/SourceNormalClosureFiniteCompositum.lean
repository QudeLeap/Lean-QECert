import QEC.Coding.AlgebraicGeometry.Towers.SourceNormalClosure

import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Finite conjugate composita for the source normal closure

The constructed source normal closure is the supremum of the field ranges of
all source embeddings into the fixed separable closure.  Its proved finite
dimension makes this intermediate field compact, so finitely many actual
conjugate field ranges already generate it.

This file records that finite compositum presentation and its elementary
empty/insert laws.  It does not choose a preferred presentation, refine the
conjugates into quadratic stages, or assert any ramification, different,
divisor, genus, or asymptotic conclusion.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- The compositum of a finite family of actual conjugate source fields in
the fixed ambient separable closure. -/
noncomputable def sourceGaloisConjugateCompositum (m : ℕ)
    (s : Finset (SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient)) :
    IntermediateField GaloisBaseField SourceGaloisClosureAmbient :=
  ⨆ f ∈ s, f.fieldRange

/-- The compositum of no conjugate source fields is the rational base. -/
theorem sourceGaloisConjugateCompositum_empty (m : ℕ) :
    sourceGaloisConjugateCompositum m ∅ = ⊥ := by
  simp [sourceGaloisConjugateCompositum]

/-- Inserting one conjugate source field adjoins its actual field range to
the preceding finite compositum. -/
theorem sourceGaloisConjugateCompositum_cons (m : ℕ)
    (s : Finset (SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient))
    (f : SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient)
    (hf : f ∉ s) :
    sourceGaloisConjugateCompositum m (s.cons f hf) =
      sourceGaloisConjugateCompositum m s ⊔ f.fieldRange := by
  unfold sourceGaloisConjugateCompositum
  apply le_antisymm
  · refine iSup_le fun g => iSup_le fun hg => ?_
    rcases Finset.mem_cons.mp hg with hgf | hgs
    · subst g
      exact le_sup_right
    · exact (le_iSup_of_le g
        (le_iSup (fun _ : g ∈ s => g.fieldRange) hgs)).trans le_sup_left
  · apply sup_le
    · refine iSup_le fun g => iSup_le fun hgs => ?_
      exact le_iSup_of_le g
        (le_iSup_of_le (Finset.mem_cons_of_mem hgs) le_rfl)
    · exact le_iSup_of_le f
        (le_iSup_of_le (Finset.mem_cons_self f s) le_rfl)

/-- Finitely many actual conjugate copies of source level `m` generate its
constructed normal closure inside the fixed separable closure. -/
theorem exists_sourceGaloisConjugateCompositum_eq_normalClosure (m : ℕ) :
    ∃ s : Finset (SourceField m →ₐ[GaloisBaseField]
        SourceGaloisClosureAmbient),
      sourceGaloisConjugateCompositum m s =
        IntermediateField.normalClosure GaloisBaseField (SourceField m)
          SourceGaloisClosureAmbient := by
  let N : IntermediateField GaloisBaseField SourceGaloisClosureAmbient :=
    IntermediateField.normalClosure GaloisBaseField (SourceField m)
      SourceGaloisClosureAmbient
  have hNfg : N.FG := by
    rw [← IntermediateField.essFiniteType_iff]
    infer_instance
  obtain ⟨t, ht⟩ := hNfg
  have hNcompact : IsCompactElement N := by
    rw [← ht]
    exact IntermediateField.adjoin_finset_isCompactElement t
  have hNle : N ≤
      ⨆ f : SourceField m →ₐ[GaloisBaseField]
        SourceGaloisClosureAmbient, f.fieldRange := by
    exact (normalClosure_def GaloisBaseField
      (SourceField m) SourceGaloisClosureAmbient).le
  obtain ⟨s, hs⟩ :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
      (IntermediateField GaloisBaseField SourceGaloisClosureAmbient) hNcompact
    (fun f : SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient => f.fieldRange) hNle
  refine ⟨s, le_antisymm ?_ hs⟩
  dsimp only [sourceGaloisConjugateCompositum]
  refine iSup_le fun f => iSup_le fun _ => ?_
  exact f.fieldRange_le_normalClosure

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
