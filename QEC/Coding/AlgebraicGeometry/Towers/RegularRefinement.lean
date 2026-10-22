import QEC.Coding.AlgebraicGeometry.Towers.TraceRefinement

/-!
# Literal regular refinements at one ambient place

Regular quadratic generators remain regular after adjoining other fields:
their equations and the same ambient valuation ring suffice. Unlike the
simple-pole square, this case needs no residue-square parameter correction.
Only equations, membership and generated fields occur in the relation.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)

/-- One actual regular quadratic generator in a fixed ambient field. -/
def RegularQuadraticEdge (K L : IntermediateField F E) : Prop :=
  ∃ y : E, y ∈ Q.valuationRing ∧ y ^ 2 + y ∈ K ∧ L = K ⊔ F⟮y⟯

theorem RegularQuadraticEdge.le {K L : IntermediateField F E}
    (h : RegularQuadraticEdge Q K L) : K ≤ L := by
  obtain ⟨y, _, _, rfl⟩ := h
  exact le_sup_left

/-- Enlarging the lower field retains the same literal regular generator. -/
theorem RegularQuadraticEdge.enlarge_base {K L M : IntermediateField F E}
    (h : RegularQuadraticEdge Q K L) (hKM : K ≤ M) :
    RegularQuadraticEdge Q M (M ⊔ L) := by
  obtain ⟨y, hy, ha, rfl⟩ := h
  refine ⟨y, hy, hKM ha, ?_⟩
  rw [← sup_assoc, sup_eq_left.mpr hKM]

/-- A finite sequence of actual regular quadratic generators. -/
abbrev RegularRefinement (K L : IntermediateField F E) : Prop :=
  Relation.ReflTransGen (RegularQuadraticEdge Q) K L

theorem RegularRefinement.le {K L : IntermediateField F E}
    (h : RegularRefinement Q K L) : K ≤ L := by
  induction h with
  | refl => exact le_rfl
  | tail h hstep ih => exact ih.trans (hstep.le Q)

theorem RegularRefinement.enlarge_base {K L M : IntermediateField F E}
    (h : RegularRefinement Q K L) (hKM : K ≤ M) :
    RegularRefinement Q M (M ⊔ L) := by
  induction h with
  | refl => rw [sup_eq_left.mpr hKM]
  | @tail L N hchain hstep ih =>
      have hs := hstep.enlarge_base Q (show L ≤ M ⊔ L from le_sup_right)
      rw [sup_assoc, sup_eq_right.mpr (hstep.le Q)] at hs
      exact ih.tail hs

theorem RegularRefinement.finset_sup {ι : Type*} (K : IntermediateField F E)
    (s : Finset ι) (L : ι → IntermediateField F E)
    (h : ∀ i ∈ s, RegularRefinement Q K (L i)) :
    RegularRefinement Q K (K ⊔ s.sup L) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty, sup_bot_eq]
  | @insert a s ha ih =>
      have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have ha' := h a (Finset.mem_insert_self a s)
      have hnew := ha'.enlarge_base Q (show K ≤ K ⊔ s.sup L from le_sup_left)
      have hresult := hs.trans hnew
      simpa only [Finset.sup_insert, sup_assoc, sup_comm, sup_left_comm] using hresult

theorem traceCoordinates16_mem_valuationRing (y : E) (hy : y ∈ Q.valuationRing) (i : ℕ) :
    traceCoordinates16 y i ∈ Q.valuationRing := by
  have hp (n : ℕ) := Q.valuationRing.pow_mem hy n
  rcases i with _ | _ | _ | _ | i
  · exact Q.valuationRing.add_mem _ _ (hp 16) hy
  · exact Q.valuationRing.add_mem _ _
      (Q.valuationRing.add_mem _ _ (Q.valuationRing.add_mem _ _ (hp 8) (hp 4)) (hp 2)) hy
  · exact Q.valuationRing.add_mem _ _ (hp 4) hy
  · exact Q.valuationRing.add_mem _ _ (hp 2) hy
  · exact hy

/-- The four actual trace coordinates give a regular refinement of an
additive degree-sixteen equation. Redundant stages are permitted. -/
theorem artinSchreier16_regularRefinement [CharP E 2]
    (K : IntermediateField F E) (y : E)
    (hy : y ∈ Q.valuationRing) (ha : y ^ 16 + y ∈ K) :
    RegularRefinement Q K (K ⊔ F⟮y⟯) := by
  let t := traceCoordinates16 y
  have ht : t 0 ∈ K := ha
  have hchain (n : ℕ) (hn : n ≤ 4) : RegularRefinement Q K (tracePrefixField K t n) := by
    induction n with
    | zero => exact .refl
    | succ n ih =>
        apply (ih (by omega)).tail
        refine ⟨t (n + 1), traceCoordinates16_mem_valuationRing Q y hy (n + 1), ?_, ?_⟩
        · rw [traceCoordinates16_equation y n (by omega)]
          exact tracePrefixField_coordinate_mem K t ht n
        · exact IntermediateField.restrictScalars_adjoin_eq_sup F _ _
  have h := hchain 4 le_rfl
  rw [tracePrefixField_eq_adjoin_terminal K t ht 4 (traceCoordinates16_equation y),
    IntermediateField.restrictScalars_adjoin_eq_sup] at h
  exact h

section ChangeBase

variable {B : Type*} [_root_.Field B] [Algebra F B] [Algebra B E]
  [IsScalarTower F B E]

theorem RegularQuadraticEdge.of_restrictScalars
    {J L : IntermediateField B E}
    (h : RegularQuadraticEdge Q (J.restrictScalars F) (L.restrictScalars F)) :
    RegularQuadraticEdge Q J L := by
  obtain ⟨y, hy, ha, hgen⟩ := h
  refine ⟨y, hy, ha, ?_⟩
  have hsmall : ((J.restrictScalars F)⟮y⟯).restrictScalars F = L.restrictScalars F := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, ← hgen]
  apply IntermediateField.restrictScalars_injective F
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup B J ({y} : Set E)]
  exact hsmall.symm

/-- Read the same regular generators over a larger common base. Every
intermediate field contains the initial field, so none is added or guessed. -/
theorem RegularRefinement.of_restrictScalars
    {J L : IntermediateField B E}
    (h : RegularRefinement Q (J.restrictScalars F) (L.restrictScalars F)) :
    RegularRefinement Q J L := by
  have hlift (N : IntermediateField F E)
      (hc : RegularRefinement Q (J.restrictScalars F) N) :
      ∃ N' : IntermediateField B E, N'.restrictScalars F = N ∧ RegularRefinement Q J N' := by
    induction hc with
    | refl => exact ⟨J, rfl, .refl⟩
    | @tail N M hchain hstep ih =>
        obtain ⟨N', hN', ih⟩ := ih
        have hJM := RegularRefinement.le Q (hchain.tail hstep)
        let M' : IntermediateField B E :=
          M.toSubfield.toIntermediateField (fun x => hJM (J.algebraMap_mem x))
        have hedge : RegularQuadraticEdge Q (N'.restrictScalars F) (M'.restrictScalars F) := by
          change RegularQuadraticEdge Q (N'.restrictScalars F) M
          rwa [hN']
        exact ⟨M', rfl, ih.tail (hedge.of_restrictScalars Q)⟩
  obtain ⟨L', hL', hc⟩ := hlift _ h
  have heq : L' = L := IntermediateField.restrictScalars_injective F hL'
  rwa [heq] at hc

end ChangeBase

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
