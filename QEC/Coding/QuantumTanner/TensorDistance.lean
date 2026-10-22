import QEC.Coding.QuantumTanner.TensorDuality

/-!
# A distance lower bound for the dual-tensor sum

The lower-bound direction of `d(C_A ⊗ F^B + F^A ⊗ C_B) = min(d_A,d_B)`
in [LZ22, Section 2, Tensor codes and dual tensor codes: robustness].
The proof uses contraction by dual codewords, not a robustness assumption.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe u v

variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

/-- Pair a fixed word with each column of a matrix. -/
def columnContraction (a : Word F A) : Word F (A × B) →ₗ[F] Word F B where
  toFun x b := wordPairing a (columnRestriction b x)
  map_add' x y := by
    ext b
    simp [map_add]
  map_smul' s x := by
    ext b
    simp [map_smul]

theorem columnContraction_eq_sum (a : Word F A) (x : Word F (A × B)) :
    columnContraction a x = ∑ i : A, a i • rowRestriction i x := by
  ext b
  simp [columnContraction, wordPairing_apply, dotProduct, columnRestriction,
    rowRestriction, Finset.sum_apply, smul_eq_mul]

/-- Contracting a dual-tensor word by a dual `C_A` word gives a `C_B` word. -/
theorem columnContraction_mem_of_mem_dualTensorCode
    (CA : LinearCode F A) (CB : LinearCode F B) (a : Word F A)
    (ha : a ∈ CA.dual.carrier) (x : Word F (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier) :
    columnContraction a x ∈ CB.carrier := by
  obtain ⟨c, hc, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  have hcZero : columnContraction a c = 0 := by
    ext b
    exact CA.orthogonal_of_mem_dual ha (hc b)
  rw [map_add, hcZero, zero_add, columnContraction_eq_sum]
  apply Submodule.sum_mem
  intro i _hi
  exact CB.carrier.smul_mem _ (hr i)

/-- Contraction cannot create a nonzero column where the original matrix is zero. -/
theorem hammingWeight_columnContraction_le [DecidableEq F]
    (a : Word F A) (x : Word F (A × B)) :
    HammingWeight (columnContraction a x) ≤ HammingWeight x := by
  have hs : hammingSupport (columnContraction a x) ⊆ (hammingSupport x).image Prod.snd := by
    intro b hb
    have hne : (columnContraction a x) b ≠ 0 := (Finset.mem_filter.mp hb).2
    have hex : ∃ i : A, x (i, b) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hne
      simp [columnContraction, wordPairing_apply, dotProduct, columnRestriction, h]
    obtain ⟨i, hi⟩ := hex
    exact Finset.mem_image.mpr ⟨(i, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le)

/-- A single column has no more nonzero coordinates than the full matrix. -/
theorem hammingWeight_columnRestriction_le [DecidableEq F]
    (b : B) (x : Word F (A × B)) :
    HammingWeight (columnRestriction b x) ≤ HammingWeight x := by
  have hs : (hammingSupport (columnRestriction b x)).image (fun a => (a, b)) ⊆
      hammingSupport x := by
    intro ab hab
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hab
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  have hinj : Function.Injective (fun a : A => (a, b)) := fun _ _ h => congrArg Prod.fst h
  have hcard := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hinj] at hcard
  exact hcard

/-- Every nonzero word of the actual row/column sum has weight at least the
minimum of the two local distance lower bounds. No nonemptiness is assumed. -/
theorem hammingWeight_ge_min_of_mem_dualTensorCode [DecidableEq F]
    (CA : LinearCode F A) (CB : LinearCode F B) (dA dB : Nat)
    (hA : ∀ a : Word F A, a ∈ CA.carrier → a ≠ 0 → dA ≤ HammingWeight a)
    (hB : ∀ b : Word F B, b ∈ CB.carrier → b ≠ 0 → dB ≤ HammingWeight b)
    (x : Word F (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier) (hne : x ≠ 0) :
    min dA dB ≤ HammingWeight x := by
  by_contra hsmall
  have hlt : HammingWeight x < min dA dB := Nat.lt_of_not_ge hsmall
  have hltA : HammingWeight x < dA := lt_of_lt_of_le hlt (min_le_left _ _)
  have hltB : HammingWeight x < dB := lt_of_lt_of_le hlt (min_le_right _ _)
  have hcolumns : ∀ b, columnRestriction b x ∈ CA.carrier := by
    intro b
    rw [← LinearCode.dual_dual_carrier_eq CA]
    refine (CA.dual.mem_dual _).2 ?_
    intro a ha
    have hcontract : columnContraction a x = 0 := by
      by_contra hc
      have hbound := hB _ (columnContraction_mem_of_mem_dualTensorCode CA CB a ha x hx) hc
      have hweight := hammingWeight_columnContraction_le a x
      omega
    have hb := congrFun hcontract b
    change wordPairing a (columnRestriction b x) = 0 at hb
    rw [wordPairing_apply, dotProduct_comm]
    exact hb
  have hxzero : x = 0 := by
    ext ab
    have hcolumn : columnRestriction ab.2 x = 0 := by
      by_contra hc
      have hbound := hA _ (hcolumns ab.2) hc
      have hweight := hammingWeight_columnRestriction_le ab.2 x
      omega
    exact congrFun hcolumn ab.1
  exact hne hxzero

end QEC.Coding.QuantumTanner
