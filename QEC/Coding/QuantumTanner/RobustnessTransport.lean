import QEC.Coding.QuantumTanner.Core

/-!
# Robustness under empty puncturing

Deleting no coordinates changes the coordinate type, but not the code,
weights, or support-cover bounds. This bridge applies the source's
puncture-resistant robustness to the original coordinates without assuming
ordinary robustness separately [LZ22, Section 2].
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe u v

/-- Retaining every coordinate is an actual equivalence of coordinate sets. -/
def emptyKeptCoordinateEquiv (I : Type v) [Fintype I] :
    KeptCoordinate (∅ : Finset I) ≃ I where
  toFun := Subtype.val
  invFun i := ⟨i, by simp⟩
  left_inv i := Subtype.ext rfl
  right_inv _ := rfl

/-- Hamming weight is unchanged by a bijection of the coordinate set. -/
theorem hammingWeight_comp_equiv
    {F : Type u} [Zero F] [DecidableEq F]
    {I J : Type v} [Fintype I] [Fintype J]
    (e : I ≃ J) (x : Word F J) :
    HammingWeight (fun i => x (e i)) = HammingWeight x := by
  simp only [HammingWeight, hammingSupport, Finset.card_filter]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- An attained minimum is unchanged by deleting the empty coordinate set. -/
theorem minimumDistance_punctured_empty
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I)
    {d : Nat} (h : MinimumDistance C d) :
    MinimumDistance (puncturedCode C ∅) d := by
  obtain ⟨x, hx, hx0, hweight, hmin⟩ := h
  have hw (y : Word (ZMod 2) I) : HammingWeight (punctureMap ∅ y) = HammingWeight y :=
    hammingWeight_comp_equiv (emptyKeptCoordinateEquiv I) y
  refine ⟨punctureMap ∅ x, (mem_puncturedCode C ∅ _).mpr ⟨x, hx, rfl⟩,
    ?_, (hw x).trans hweight, ?_⟩
  · intro hz
    apply hx0
    ext i
    exact congrFun hz ⟨i, by simp⟩
  · intro y hy hy0
    obtain ⟨z, hz, rfl⟩ := (mem_puncturedCode C ∅ y).mp hy
    rw [hw]
    apply hmin z hz
    intro hz0
    apply hy0
    rw [hz0, map_zero]

/-- Restricting both coordinates along empty punctures preserves actual
membership in the row/column sum code. -/
theorem dualTensorCode_mem_punctured_empty
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier) :
    (fun ab : KeptCoordinate (∅ : Finset A) × KeptCoordinate (∅ : Finset B) =>
      x (ab.1.1, ab.2.1)) ∈ (dualTensorCode (puncturedCode CA ∅) (puncturedCode CB ∅)).carrier := by
  obtain ⟨c, hc, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  apply Submodule.mem_sup.mpr
  refine ⟨(fun ab => c (ab.1.1, ab.2.1)), ?_,
    (fun ab => r (ab.1.1, ab.2.1)), ?_, rfl⟩
  · intro b
    exact (mem_puncturedCode CA ∅ _).mpr ⟨columnRestriction b.1 c, hc b.1, rfl⟩
  · intro a
    exact (mem_puncturedCode CB ∅ _).mpr ⟨rowRestriction a.1 r, hr a.1, rfl⟩

/-- Puncture resistance includes ordinary robustness, with the original
minimum distances and the exact original support-cover bounds. -/
theorem IsRobustWithPunctureResistance.isRobust
    {A B : Type v} [Fintype A] [Fintype B]
    {CA : LinearCode (ZMod 2) A} {CB : LinearCode (ZMod 2) B}
    {w p : Nat} (h : IsRobustWithPunctureResistance CA CB w p) :
    IsRobust CA CB w := by
  intro dA dB hA hB x hx hweight
  let y : Word (ZMod 2)
      (KeptCoordinate (∅ : Finset A) × KeptCoordinate (∅ : Finset B)) :=
    fun ab => x (ab.1.1, ab.2.1)
  have hw : HammingWeight y = HammingWeight x :=
    hammingWeight_comp_equiv
      ((emptyKeptCoordinateEquiv A).prodCongr (emptyKeptCoordinateEquiv B)) x
  obtain ⟨rows, columns, hcover, hrows, hcolumns⟩ :=
    h ∅ ∅ rfl (Nat.zero_le p) dA dB
      (minimumDistance_punctured_empty CA hA) (minimumDistance_punctured_empty CB hB)
      y (dualTensorCode_mem_punctured_empty CA CB x hx) (hw ▸ hweight)
  refine ⟨rows.image Subtype.val, columns.image Subtype.val, ?_, ?_, ?_⟩
  · intro ab hab
    have hy : (⟨ab.1, by simp⟩, ⟨ab.2, by simp⟩) ∈ hammingSupport y := by
      simpa only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and, y] using hab
    have hc := hcover hy
    simp only [Finset.mem_union, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ,
      and_true, true_and] at hc ⊢
    exact hc.elim
      (fun ha => Or.inl (Finset.mem_image.mpr
        ⟨(⟨ab.1, by simp⟩ : KeptCoordinate (∅ : Finset A)), ha, rfl⟩))
      (fun hb => Or.inr (Finset.mem_image.mpr
        ⟨(⟨ab.2, by simp⟩ : KeptCoordinate (∅ : Finset B)), hb, rfl⟩))
  · exact Finset.card_image_le.trans (hw ▸ hrows)
  · exact Finset.card_image_le.trans (hw ▸ hcolumns)

end QEC.Coding.QuantumTanner
