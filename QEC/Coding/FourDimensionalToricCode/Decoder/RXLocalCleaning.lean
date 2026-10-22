import QEC.Coding.FourDimensionalToricCode.Decoder.Multiscale

/-!
# RX local-cleaning adapters

This module is the decoder-facing slice of the audited BDL26 construction
contract.  It does not construct any local block.  M13 supplies the four
contract fields (`rx_local_complexes`, `rx_local_cohomology`,
`support_decomposition`, and `local_boundary_weight_budgets`); the present
module only assembles those finite interfaces and proves the two aggregate
weight inequalities.
-/

namespace QEC
namespace Coding
namespace MultiscaleDecoder

open scoped BigOperators

universe u v w x y z a b c

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]

/-! ## Finite-word support lemmas -/

theorem hammingSupport_add_of_disjoint
    {F : Type u} {ι : Type v} [AddGroup F] [DecidableEq F] [Fintype ι]
    [DecidableEq ι]
    (x y : Word F ι)
    (hxy : Disjoint (hammingSupport x) (hammingSupport y)) :
    hammingSupport (x + y) = hammingSupport x ∪ hammingSupport y := by
  classical
  ext i
  by_cases hxi : x i = 0
  · by_cases hyi : y i = 0
    · simp [hammingSupport, hxi, hyi]
    · have hiy : i ∈ hammingSupport y := by simp [hammingSupport, hyi]
      have hix : i ∉ hammingSupport x := by
        intro hi
        exact (Finset.disjoint_left.1 hxy) hi hiy
      simp [hammingSupport, hxi, hyi, hix]
  · have hix : i ∈ hammingSupport x := by simp [hammingSupport, hxi]
    have hyi : y i = 0 := by
      by_contra hne
      have hiy : i ∈ hammingSupport y := by simp [hammingSupport, hne]
      exact (Finset.disjoint_left.1 hxy) hix hiy
    simp [hammingSupport, hxi, hyi]

theorem HammingWeight_add_of_disjoint
    {F : Type u} {ι : Type v} [AddGroup F] [DecidableEq F] [Fintype ι]
    [DecidableEq ι]
    (x y : Word F ι)
    (hxy : Disjoint (hammingSupport x) (hammingSupport y)) :
    HammingWeight (x + y) = HammingWeight x + HammingWeight y := by
  rw [HammingWeight_eq_card_hammingSupport,
    hammingSupport_add_of_disjoint x y hxy,
    Finset.card_union_of_disjoint hxy,
    ← HammingWeight_eq_card_hammingSupport x,
    ← HammingWeight_eq_card_hammingSupport y]

theorem HammingWeight_finset_sum_le
    {F : Type u} {ι : Type v} {κ : Type w}
    [AddCommGroup F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Fintype κ]
    (s : Finset κ) (f : κ → Word F ι) :
    HammingWeight (∑ k ∈ s, f k) ≤ ∑ k ∈ s, HammingWeight (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      exact (HammingWeight_add_le (f k) (∑ j ∈ s, f j)).trans
        (Nat.add_le_add_left ih (HammingWeight (f k)))

theorem HammingWeight_univ_sum_le
    {F : Type u} {ι : Type v} {κ : Type w}
    [AddCommGroup F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Fintype κ]
    (f : κ → Word F ι) :
    HammingWeight (∑ k : κ, f k) ≤ ∑ k : κ, HammingWeight (f k) := by
  simpa using HammingWeight_finset_sum_le (Finset.univ : Finset κ) f

/-! ## Linear restriction/extension adapters -/

noncomputable def restrictWordLinear
    {F : Type u} [Field F] {ι : Type v} [Fintype ι]
    (Y : Finset ι) : Word F ι →ₗ[F] Word F (LocalRegionIndex Y) where
  toFun := fun signal => restrictLocalSignal Y signal
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl

noncomputable def extendWordLinear
    {F : Type u} [Field F] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (Y : Finset ι) : Word F (LocalRegionIndex Y) →ₗ[F] Word F ι where
  toFun := fun signal => extendLocalSignal Y signal
  map_add' := by
    intro x y
    funext i
    by_cases hi : i ∈ Y <;> simp [extendLocalSignal, hi]
  map_smul' := by
    intro r x
    funext i
    by_cases hi : i ∈ Y <;> simp [extendLocalSignal, hi]

noncomputable def outsideMaskWord
    {F : Type u} {ι : Type v} [Zero F] [Fintype ι] [DecidableEq ι]
    (Y : Finset ι) (signal : Word F ι) : Word F ι :=
  maskWord (Finset.univ \ Y) signal

theorem outsideMaskWord_add_maskWord
    {F : Type u} [AddGroup F] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (Y : Finset ι) (signal : Word F ι) :
    outsideMaskWord Y signal + maskWord Y signal = signal := by
  funext i
  by_cases hi : i ∈ Y <;> simp [outsideMaskWord, maskWord, hi]

theorem hammingSupport_extendWordLinear
    {F : Type u} [Field F] [DecidableEq F] {ι : Type v} [Fintype ι]
    [DecidableEq ι]
    (Y : Finset ι) (signal : Word F (LocalRegionIndex Y)) :
    hammingSupport (extendWordLinear Y signal) =
      Finset.image Subtype.val (hammingSupport signal) := by
  classical
  ext i
  by_cases hi : i ∈ Y
  · let ui : LocalRegionIndex Y := ⟨i, hi⟩
    simp [extendWordLinear, extendLocalSignal, hi,
      hammingSupport, ui]
  · simp [extendWordLinear, extendLocalSignal, hi,
      hammingSupport]

theorem HammingWeight_extendWordLinear
    {F : Type u} [Field F] [DecidableEq F] {ι : Type v} [Fintype ι]
    [DecidableEq ι]
    (Y : Finset ι) (signal : Word F (LocalRegionIndex Y)) :
    HammingWeight (extendWordLinear Y signal) = HammingWeight signal := by
  rw [HammingWeight_eq_card_hammingSupport,
    hammingSupport_extendWordLinear Y signal]
  simpa [HammingWeight] using
    (Finset.card_image_iff.mpr (by
      intro x hx y hy hxy
      exact Subtype.ext hxy))

private theorem hammingSupport_sum_subset_biUnion
    {F : Type u} {ι : Type v} {κ : Type w}
    [AddCommGroup F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Fintype κ]
    (s : Finset κ) (f : κ → Word F ι) :
    hammingSupport (∑ k ∈ s, f k) ⊆
      s.biUnion (fun k => hammingSupport (f k)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      intro i hi
      have hsub := hammingSupport_add_subset_union (f k) (∑ j ∈ s, f j)
      have hi' := hsub (by simpa [Finset.sum_insert hk] using hi)
      simp only [Finset.mem_union] at hi'
      rcases hi' with hiK | hiS
      · simp [hiK, hk]
      · have hiBi := ih hiS
        simp only [Finset.mem_union, Finset.mem_biUnion] at hiBi ⊢
        rcases hiBi with ⟨j, hjS, hij⟩
        exact ⟨j, by simp [hjS, hk], hij⟩

theorem HammingWeight_extend_restrict_sum
    {F : Type u} {ι : Type v} {κ : Type w}
    [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (regions : κ → Finset ι)
    (hdisj : ∀ a b, a ≠ b → Disjoint (regions a) (regions b))
    (signal : Word F ι) :
    HammingWeight (∑ k : κ,
      extendWordLinear (regions k) (restrictWordLinear (regions k) signal)) =
      ∑ k : κ, HammingWeight (restrictWordLinear (regions k) signal) := by
  classical
  let term : κ → Word F ι := fun k =>
    extendWordLinear (regions k) (restrictWordLinear (regions k) signal)
  have hterm_support_subset : ∀ k, hammingSupport (term k) ⊆ regions k := by
    intro k i hi
    by_cases hik : i ∈ regions k
    · exact hik
    · have hz : term k i = 0 := by
        simp [term, extendWordLinear, extendLocalSignal, hik]
      have hne : term k i ≠ 0 := by
        simpa [hammingSupport] using hi
      exact (hne hz).elim
  have hsum : ∀ (s : Finset κ),
      HammingWeight (∑ k ∈ s, term k) =
        ∑ k ∈ s, HammingWeight (term k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        calc
          HammingWeight (term k + ∑ j ∈ s, term j) =
              HammingWeight (term k) +
                HammingWeight (∑ j ∈ s, term j) := by
            apply HammingWeight_add_of_disjoint
            refine Finset.disjoint_left.2 ?_
            intro i hiK hiS
            have hiKreg := hterm_support_subset k hiK
            have hiSbi := hammingSupport_sum_subset_biUnion s term hiS
            rcases Finset.mem_biUnion.mp hiSbi with ⟨j, hjS, hij⟩
            exact (Finset.disjoint_left.1 (hdisj k j (by
              intro hkj
              subst j
              exact hk hjS))) hiKreg (hterm_support_subset j hij)
          _ = HammingWeight (term k) +
              ∑ j ∈ s, HammingWeight (term j) := by rw [ih]
  rw [show (∑ k : κ, term k) = ∑ k ∈ (Finset.univ : Finset κ), term k by rfl,
    hsum]
  simp only [term]
  apply Finset.sum_congr rfl
  intro k hk
  exact HammingWeight_extendWordLinear _ _

noncomputable def rxRegionUnion
    {V : Type v} {S C : Type w} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (L : LocalComplexData V S C) : Finset S :=
  Finset.biUnion Finset.univ (fun v => L.syndromeRegion v)

noncomputable def rxLocalPart
    {V : Type v} {S C : Type w} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (L : LocalComplexData V S C) (sigma : Word BDL26Field S) : Word BDL26Field S :=
  ∑ v : V, extendWordLinear (L.syndromeRegion v)
    (restrictWordLinear (L.syndromeRegion v) sigma)

noncomputable def rxResidual
    {V : Type v} {S C : Type w} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (L : LocalComplexData V S C) (sigma : Word BDL26Field S) : Word BDL26Field S :=
  outsideMaskWord (rxRegionUnion L) sigma

theorem hammingSupport_outsideMaskWord_disjoint
    {F : Type u} {ι : Type v} [AddGroup F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (Y : Finset ι) (signal : Word F ι) :
    Disjoint (hammingSupport (outsideMaskWord Y signal))
      (hammingSupport (maskWord Y signal)) := by
  refine Finset.disjoint_left.2 ?_
  intro i hiOutside hiInside
  have hnot : i ∉ Y := by
    have htmp : i ∉ Y ∧ signal i ≠ 0 := by
      simpa [outsideMaskWord, maskWord, hammingSupport] using hiOutside
    exact htmp.1
  have hin : i ∈ Y := by
    have htmp : i ∈ Y ∧ signal i ≠ 0 := by
      simpa [outsideMaskWord, maskWord, hammingSupport] using hiInside
    exact htmp.1
  exact hnot hin

theorem extend_restrict_sum_eq_mask
    {F : Type u} {ι : Type v} {κ : Type w}
    [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (regions : κ → Finset ι)
    (hdisj : ∀ a b, a ≠ b → Disjoint (regions a) (regions b))
    (signal : Word F ι) :
    (∑ k : κ, extendWordLinear (regions k)
      (restrictWordLinear (regions k) signal)) =
      maskWord (Finset.biUnion Finset.univ regions) signal := by
  classical
  funext i
  by_cases hi : i ∈ Finset.biUnion (Finset.univ : Finset κ) regions
  · rcases Finset.mem_biUnion.mp hi with ⟨k, hk, hik⟩
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp [extendWordLinear, restrictWordLinear, extendLocalSignal,
        restrictLocalSignal, hik, maskWord, hi]
      rfl
    · intro j hj hne
      have hnot : i ∉ regions j := by
        intro hij
        exact (Finset.disjoint_left.1 (hdisj k j (by
          intro hkj
          subst j
          exact hne rfl))) hik hij
      simp [extendWordLinear, restrictWordLinear, extendLocalSignal,
        restrictLocalSignal, hnot]
    · simp [maskWord, hi]
  · have hz : ∀ k : κ, k ∈ Finset.univ →
      extendWordLinear (regions k)
        (restrictWordLinear (regions k) signal) i = 0 := by
      intro k hk
      have hnot : i ∉ regions k := by
        intro hik
        exact hi (Finset.mem_biUnion.mpr ⟨k, hk, hik⟩)
      simp [extendWordLinear, restrictWordLinear, extendLocalSignal,
        restrictLocalSignal, hnot]
    simp only [Finset.sum_apply]
    simp [maskWord, hi, hz]

/-! ## Contract data records -/

structure RXLocalComplexData
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    {X Q Z : Type v}
    [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    (Lx : LocalComplexData X (C2 i.succ) (C1 i.succ))
    (Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ))
    (Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)) where
  cx : ∀ x, ChainComplexData BDL26Field
      (Word BDL26Field (X0 x))
      (Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)))
      (Word BDL26Field (LocalRegionIndex (Lx.syndromeRegion x)))
  cq : ∀ q, ChainComplexData BDL26Field
      (Word BDL26Field (Q0 q))
      (Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q)))
      (Word BDL26Field (LocalRegionIndex (Lq.syndromeRegion q)))
  cz : ∀ z, ChainComplexData BDL26Field
      (Word BDL26Field (Z0 z))
      (Word BDL26Field (Z1 z))
      (Word BDL26Field (Z2 z))

namespace RXLocalComplexData

variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable (K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)

noncomputable abbrev cxDelta0 (x : X) :
    Word BDL26Field (X0 x) →ₗ[BDL26Field]
      Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)) :=
  wordLinearMapTranspose (K.cx x).boundary1

noncomputable abbrev cxDelta1 (x : X) :
    Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)) →ₗ[BDL26Field]
      Word BDL26Field (LocalRegionIndex (Lx.syndromeRegion x)) :=
  wordLinearMapTranspose (K.cx x).boundary2

noncomputable abbrev cqDelta0 (q : Q) :
    Word BDL26Field (Q0 q) →ₗ[BDL26Field]
      Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q)) :=
  wordLinearMapTranspose (K.cq q).boundary1

noncomputable abbrev cqDelta1 (q : Q) :
    Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q)) →ₗ[BDL26Field]
      Word BDL26Field (LocalRegionIndex (Lq.syndromeRegion q)) :=
  wordLinearMapTranspose (K.cq q).boundary2

end RXLocalComplexData

variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}

structure RXLocalCohomology
    (K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz) where
  /-- The quotient/ker=range identification `H¹(C_x)=0`. -/
  cx_h1_ker_eq_range :
    ∀ x, LinearMap.ker (K.cxDelta1 x) = LinearMap.range (K.cxDelta0 x)
  /-- The displayed `H¹(C_q)=F₂` dimension; representatives stay M13 data. -/
  cq_h1_finrank :
    ∀ q, Module.finrank BDL26Field (K.cq q).middleCohomology = 1

structure RXSupportDecomposition
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
    {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
    {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
    (K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz) where
  cxFlow : ∀ x, Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)) →ₗ[BDL26Field]
    D.family.Cochain2 i.succ
  cqFlow : ∀ q, Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q)) →ₗ[BDL26Field]
    D.family.Cochain2 i.succ
  cxLift0 : ∀ x, Word BDL26Field (X0 x) →ₗ[BDL26Field] D.family.Cochain0 i.succ
  cqLift0 : ∀ q, Word BDL26Field (Q0 q) →ₗ[BDL26Field] D.family.Cochain0 i.succ
  cxDelta1_restriction : ∀ x f,
    restrictWordLinear (Lx.syndromeRegion x)
        (D.family.coboundary1 i.succ
          (extendWordLinear (Lx.correctionRegion x) f)) = K.cxDelta1 x f
  cxDelta1_restriction_global : ∀ x error,
    restrictWordLinear (Lx.syndromeRegion x)
        (D.family.coboundary1 i.succ error) =
      K.cxDelta1 x (restrictWordLinear (Lx.correctionRegion x) error)
  cqDelta1_restriction : ∀ q f,
    restrictWordLinear (Lq.syndromeRegion q)
        (D.family.coboundary1 i.succ
          (extendWordLinear (Lq.correctionRegion q) f)) = K.cqDelta1 q f
  /-- Q restriction is valid after the actual X error has been removed. -/
  cqDelta1_restriction_global : ∀ q error,
    (∀ x, restrictWordLinear (Lx.correctionRegion x) error = 0) →
    restrictWordLinear (Lq.syndromeRegion q)
        (D.family.coboundary1 i.succ error) =
      K.cqDelta1 q (restrictWordLinear (Lq.correctionRegion q) error)
  cxDelta0_restriction : ∀ x s,
    restrictWordLinear (Lx.correctionRegion x)
        (D.family.coboundary0 i.succ (cxLift0 x s)) = K.cxDelta0 x s
  cxDelta0_sum_decomposition : ∀ (s : ∀ x, Word BDL26Field (X0 x)) x,
    restrictWordLinear (Lx.correctionRegion x)
        (D.family.coboundary0 i.succ
          (∑ y : X, cxLift0 y (s y))) = K.cxDelta0 x (s x)
  cxDelta1_decomposition : ∀ x f,
    D.family.coboundary1 i.succ
        (extendWordLinear (Lx.correctionRegion x) f) =
      extendWordLinear (Lx.syndromeRegion x) (K.cxDelta1 x f) + cxFlow x f
  cqDelta1_decomposition : ∀ q f,
    D.family.coboundary1 i.succ
        (extendWordLinear (Lq.correctionRegion q) f) =
      extendWordLinear (Lq.syndromeRegion q) (K.cqDelta1 q f) + cqFlow q f
  cxFlow_outside_x_sector : ∀ x f,
    ∀ y ∈ rxRegionUnion Lx, cxFlow x f y = 0
  cqFlow_outside_q_sector : ∀ q f,
    ∀ y ∈ rxRegionUnion Lq, cqFlow q f y = 0
  cx_regions_pairwise_disjoint :
    ∀ x y, x ≠ y → Disjoint (Lx.syndromeRegion x) (Lx.syndromeRegion y)
  cq_regions_pairwise_disjoint :
    ∀ q r, q ≠ r → Disjoint (Lq.syndromeRegion q) (Lq.syndromeRegion r)

namespace RXSupportDecomposition

variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable {K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz}

theorem cx_partition (S : RXSupportDecomposition D i K)
    (sigma : D.family.Cochain2 i.succ) :
    sigma = rxResidual Lx sigma + rxLocalPart Lx sigma := by
  rw [rxResidual, rxLocalPart,
    extend_restrict_sum_eq_mask (fun x => Lx.syndromeRegion x)
      S.cx_regions_pairwise_disjoint]
  exact (outsideMaskWord_add_maskWord _ _).symm

theorem cq_partition (S : RXSupportDecomposition D i K)
    (sigma : D.family.Cochain2 i.succ) :
    sigma = rxResidual Lq sigma + rxLocalPart Lq sigma := by
  rw [rxResidual, rxLocalPart,
    extend_restrict_sum_eq_mask (fun q => Lq.syndromeRegion q)
      S.cq_regions_pairwise_disjoint]
  exact (outsideMaskWord_add_maskWord _ _).symm

theorem cx_local_part_weight (S : RXSupportDecomposition D i K)
    (sigma : D.family.Cochain2 i.succ) :
    HammingWeight (rxLocalPart Lx sigma) =
      ∑ x : X, HammingWeight
        (restrictWordLinear (Lx.syndromeRegion x) sigma) := by
  unfold rxLocalPart
  exact HammingWeight_extend_restrict_sum
    (fun x => Lx.syndromeRegion x) S.cx_regions_pairwise_disjoint sigma

theorem cq_local_part_weight (S : RXSupportDecomposition D i K)
    (sigma : D.family.Cochain2 i.succ) :
    HammingWeight (rxLocalPart Lq sigma) =
      ∑ q : Q, HammingWeight
        (restrictWordLinear (Lq.syndromeRegion q) sigma) := by
  unfold rxLocalPart
  exact HammingWeight_extend_restrict_sum
    (fun q => Lq.syndromeRegion q) S.cq_regions_pairwise_disjoint sigma

theorem cx_residual_local_weight (S : RXSupportDecomposition D i K)
    (sigma : D.family.Cochain2 i.succ) :
    HammingWeight (rxResidual Lx sigma) + HammingWeight (rxLocalPart Lx sigma) =
      HammingWeight sigma := by
  unfold rxResidual rxLocalPart
  rw [extend_restrict_sum_eq_mask
    (fun x => Lx.syndromeRegion x) S.cx_regions_pairwise_disjoint sigma]
  simp only [rxRegionUnion]
  rw [← HammingWeight_add_of_disjoint
    (outsideMaskWord (Finset.biUnion Finset.univ (fun x => Lx.syndromeRegion x)) sigma)
      (maskWord (Finset.biUnion Finset.univ (fun x => Lx.syndromeRegion x)) sigma)
      (hammingSupport_outsideMaskWord_disjoint _ _)]
  rw [outsideMaskWord_add_maskWord]

theorem cq_residual_local_weight (S : RXSupportDecomposition D i K)
    (sigma : D.family.Cochain2 i.succ) :
    HammingWeight (rxResidual Lq sigma) + HammingWeight (rxLocalPart Lq sigma) =
      HammingWeight sigma := by
  unfold rxResidual rxLocalPart
  rw [extend_restrict_sum_eq_mask
    (fun q => Lq.syndromeRegion q) S.cq_regions_pairwise_disjoint sigma]
  simp only [rxRegionUnion]
  rw [← HammingWeight_add_of_disjoint
    (outsideMaskWord (Finset.biUnion Finset.univ (fun q => Lq.syndromeRegion q)) sigma)
      (maskWord (Finset.biUnion Finset.univ (fun q => Lq.syndromeRegion q)) sigma)
      (hammingSupport_outsideMaskWord_disjoint _ _)]
  rw [outsideMaskWord_add_maskWord]

end RXSupportDecomposition

structure RXLocalBoundaryWeightBudgets
    (K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (S : RXSupportDecomposition (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i K) where
  cx : ∀ x s,
    s ∈ LinearMap.range (K.cxDelta1 x) →
      ∃ f,
        K.cxDelta1 x f = s ∧
          HammingWeight (S.cxFlow x f) ≤ HammingWeight s
  cq : ∀ q s,
    s ∈ LinearMap.range (K.cqDelta1 q) →
      ∃ f,
        K.cqDelta1 q f = s ∧
          HammingWeight (S.cqFlow q f) ≤ HammingWeight s

/-- The named four-field RX slice of the #809 construction contract. -/
structure RXConstructionContractSlice
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    (Lx : LocalComplexData X (C2 i.succ) (C1 i.succ))
    (Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ))
    (Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)) where
  /-- #809 `rx_local_complexes` (M13 F04). -/
  rx_local_complexes : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz
  /-- #809 `rx_local_cohomology` (M13 F06). -/
  rx_local_cohomology : RXLocalCohomology rx_local_complexes
  /-- #809 `support_decomposition` (M13 F11). -/
  support_decomposition : RXSupportDecomposition D i rx_local_complexes
  /-- #809 `local_boundary_weight_budgets` (M13 F12). -/
  local_boundary_weight_budgets :
    RXLocalBoundaryWeightBudgets rx_local_complexes support_decomposition

namespace RXConstructionContractSlice

variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}

private noncomputable def cxWitness
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ x,
      restrictWordLinear (Lx.syndromeRegion x) sigma ∈
        LinearMap.range (K.rx_local_complexes.cxDelta1 x)) :
    ∀ x, Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)) :=
  fun x => Classical.choose (K.local_boundary_weight_budgets.cx x
    (restrictWordLinear (Lx.syndromeRegion x) sigma) (hlocal x))

private theorem cxWitness_spec
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ x,
      restrictWordLinear (Lx.syndromeRegion x) sigma ∈
        LinearMap.range (K.rx_local_complexes.cxDelta1 x)) :
    ∀ x,
      K.rx_local_complexes.cxDelta1 x (cxWitness K sigma hlocal x) =
        restrictWordLinear (Lx.syndromeRegion x) sigma ∧
      HammingWeight (K.support_decomposition.cxFlow x
        (cxWitness K sigma hlocal x)) ≤
        HammingWeight (restrictWordLinear (Lx.syndromeRegion x) sigma) := by
  intro x
  exact Classical.choose_spec (K.local_boundary_weight_budgets.cx x
    (restrictWordLinear (Lx.syndromeRegion x) sigma) (hlocal x))

private theorem cqWitness_spec
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q,
      restrictWordLinear (Lq.syndromeRegion q) sigma ∈
        LinearMap.range (K.rx_local_complexes.cqDelta1 q)) :
    ∀ q,
      K.rx_local_complexes.cqDelta1 q (Classical.choose
        (K.local_boundary_weight_budgets.cq q
          (restrictWordLinear (Lq.syndromeRegion q) sigma) (hlocal q))) =
        restrictWordLinear (Lq.syndromeRegion q) sigma ∧
      HammingWeight (K.support_decomposition.cqFlow q (Classical.choose
        (K.local_boundary_weight_budgets.cq q
          (restrictWordLinear (Lq.syndromeRegion q) sigma) (hlocal q)))) ≤
        HammingWeight (restrictWordLinear (Lq.syndromeRegion q) sigma) := by
  intro q
  exact Classical.choose_spec (K.local_boundary_weight_budgets.cq q
    (restrictWordLinear (Lq.syndromeRegion q) sigma) (hlocal q))

theorem cx_cleaned_syndrome_weight_nonincrease
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ x,
      restrictWordLinear (Lx.syndromeRegion x) sigma ∈
        LinearMap.range (K.rx_local_complexes.cxDelta1 x)) :
    ∃ correction : D.family.Correction i.succ,
      HammingWeight
          (sigma + D.family.coboundary1 i.succ correction) ≤
        HammingWeight sigma ∧
      ∀ y ∈ rxRegionUnion Lx,
        (sigma + D.family.coboundary1 i.succ correction) y = 0 := by
  let f := cxWitness K sigma hlocal
  let correction : D.family.Correction i.succ :=
    ∑ x : X, extendWordLinear (Lx.correctionRegion x) (f x)
  let flow : D.family.Cochain2 i.succ :=
    ∑ x : X, K.support_decomposition.cxFlow x (f x)
  have hdelta : D.family.coboundary1 i.succ correction =
      rxLocalPart Lx sigma + flow := by
    dsimp [correction, flow, rxLocalPart, f]
    calc
      D.family.coboundary1 i.succ
          (∑ x : X, extendWordLinear (Lx.correctionRegion x)
            (cxWitness K sigma hlocal x)) =
          ∑ x : X, D.family.coboundary1 i.succ
            (extendWordLinear (Lx.correctionRegion x)
              (cxWitness K sigma hlocal x)) := by rw [map_sum]
      _ = ∑ x : X,
          (extendWordLinear (Lx.syndromeRegion x)
              (K.rx_local_complexes.cxDelta1 x
                (cxWitness K sigma hlocal x)) +
            K.support_decomposition.cxFlow x (cxWitness K sigma hlocal x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact K.support_decomposition.cxDelta1_decomposition x
            (cxWitness K sigma hlocal x)
      _ = rxLocalPart Lx sigma + flow := by
          rw [Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          rw [(cxWitness_spec K sigma hlocal x).1]
  have hclean : sigma + D.family.coboundary1 i.succ correction =
      rxResidual Lx sigma + flow := by
    calc
      sigma + D.family.coboundary1 i.succ correction =
          sigma + (rxLocalPart Lx sigma + flow) := by rw [hdelta]
      _ = (rxResidual Lx sigma + rxLocalPart Lx sigma) +
            (rxLocalPart Lx sigma + flow) := by
              exact congrArg (fun t => t + (rxLocalPart Lx sigma + flow))
                (RXSupportDecomposition.cx_partition K.support_decomposition sigma)
      _ = rxResidual Lx sigma + flow := by
        have htwo : rxLocalPart Lx sigma + rxLocalPart Lx sigma =
            (0 : D.family.Cochain2 i.succ) := by
          ext j
          exact ZModModule.add_self _
        calc
          (rxResidual Lx sigma + rxLocalPart Lx sigma) +
              (rxLocalPart Lx sigma + flow) =
              rxResidual Lx sigma +
                (rxLocalPart Lx sigma + rxLocalPart Lx sigma) + flow := by
                abel
          _ = rxResidual Lx sigma + 0 + flow := by rw [htwo]
          _ = rxResidual Lx sigma + flow := by simp
  have hflow : HammingWeight flow ≤ HammingWeight (rxLocalPart Lx sigma) := by
    calc
      HammingWeight flow ≤ ∑ x : X,
          HammingWeight (K.support_decomposition.cxFlow x (f x)) := by
            exact HammingWeight_univ_sum_le _
      _ ≤ ∑ x : X, HammingWeight
          (restrictWordLinear (Lx.syndromeRegion x) sigma) := by
            apply Finset.sum_le_sum
            intro x hx
            exact (cxWitness_spec K sigma hlocal x).2
      _ = HammingWeight (rxLocalPart Lx sigma) :=
        (RXSupportDecomposition.cx_local_part_weight
          K.support_decomposition sigma).symm
  refine ⟨correction, ?_, ?_⟩
  · calc
      HammingWeight (sigma + D.family.coboundary1 i.succ correction) =
          HammingWeight (rxResidual Lx sigma + flow) := by rw [hclean]
      _ ≤ HammingWeight (rxResidual Lx sigma) + HammingWeight flow :=
        HammingWeight_add_le _ _
      _ ≤ HammingWeight (rxResidual Lx sigma) +
          HammingWeight (rxLocalPart Lx sigma) := Nat.add_le_add_left hflow _
      _ = HammingWeight sigma :=
        RXSupportDecomposition.cx_residual_local_weight
          K.support_decomposition sigma
  · intro y hy
    rw [hclean]
    have hres : rxResidual Lx sigma y = 0 := by
      simp [rxResidual, outsideMaskWord, maskWord, hy]
    have hflow : flow y = 0 := by
      dsimp [flow]
      simp only [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro x hx
      exact K.support_decomposition.cxFlow_outside_x_sector
        x (cxWitness K sigma hlocal x) y hy
    change rxResidual Lx sigma y + flow y = 0
    rw [hres, hflow, add_zero]

theorem cq_cleaned_syndrome_weight_nonincrease
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q,
      restrictWordLinear (Lq.syndromeRegion q) sigma ∈
        LinearMap.range (K.rx_local_complexes.cqDelta1 q)) :
    ∃ correction : D.family.Correction i.succ,
      HammingWeight
          (sigma + D.family.coboundary1 i.succ correction) ≤
        HammingWeight sigma ∧
      ∀ y ∈ rxRegionUnion Lq,
        (sigma + D.family.coboundary1 i.succ correction) y = 0 := by
  let f : ∀ q, Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q)) :=
    fun q => Classical.choose (K.local_boundary_weight_budgets.cq q
      (restrictWordLinear (Lq.syndromeRegion q) sigma) (hlocal q))
  let correction : D.family.Correction i.succ :=
    ∑ q : Q, extendWordLinear (Lq.correctionRegion q) (f q)
  let flow : D.family.Cochain2 i.succ :=
    ∑ q : Q, K.support_decomposition.cqFlow q (f q)
  have hdelta : D.family.coboundary1 i.succ correction =
      rxLocalPart Lq sigma + flow := by
    dsimp [correction, flow, rxLocalPart, f]
    calc
      D.family.coboundary1 i.succ
          (∑ q : Q, extendWordLinear (Lq.correctionRegion q) (f q)) =
          ∑ q : Q, D.family.coboundary1 i.succ
            (extendWordLinear (Lq.correctionRegion q) (f q)) := by rw [map_sum]
      _ = ∑ q : Q,
          (extendWordLinear (Lq.syndromeRegion q)
              (K.rx_local_complexes.cqDelta1 q (f q)) +
            K.support_decomposition.cqFlow q (f q)) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact K.support_decomposition.cqDelta1_decomposition q (f q)
      _ = rxLocalPart Lq sigma + flow := by
          rw [Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro q hq
          rw [(cqWitness_spec K sigma hlocal q).1]
  have hclean : sigma + D.family.coboundary1 i.succ correction =
      rxResidual Lq sigma + flow := by
    calc
      sigma + D.family.coboundary1 i.succ correction =
          sigma + (rxLocalPart Lq sigma + flow) := by rw [hdelta]
      _ = (rxResidual Lq sigma + rxLocalPart Lq sigma) +
            (rxLocalPart Lq sigma + flow) := by
              exact congrArg (fun t => t + (rxLocalPart Lq sigma + flow))
                (RXSupportDecomposition.cq_partition K.support_decomposition sigma)
      _ = rxResidual Lq sigma + flow := by
        have htwo : rxLocalPart Lq sigma + rxLocalPart Lq sigma =
            (0 : D.family.Cochain2 i.succ) := by
          ext j
          exact ZModModule.add_self _
        calc
          (rxResidual Lq sigma + rxLocalPart Lq sigma) +
              (rxLocalPart Lq sigma + flow) =
              rxResidual Lq sigma +
                (rxLocalPart Lq sigma + rxLocalPart Lq sigma) + flow := by
                abel
          _ = rxResidual Lq sigma + 0 + flow := by rw [htwo]
          _ = rxResidual Lq sigma + flow := by simp
  have hflow : HammingWeight flow ≤ HammingWeight (rxLocalPart Lq sigma) := by
    calc
      HammingWeight flow ≤ ∑ q : Q,
          HammingWeight (K.support_decomposition.cqFlow q (f q)) := by
            exact HammingWeight_univ_sum_le _
      _ ≤ ∑ q : Q, HammingWeight
          (restrictWordLinear (Lq.syndromeRegion q) sigma) := by
            apply Finset.sum_le_sum
            intro q hq
            exact (cqWitness_spec K sigma hlocal q).2
      _ = HammingWeight (rxLocalPart Lq sigma) :=
        (RXSupportDecomposition.cq_local_part_weight
          K.support_decomposition sigma).symm
  refine ⟨correction, ?_, ?_⟩
  · calc
      HammingWeight (sigma + D.family.coboundary1 i.succ correction) =
          HammingWeight (rxResidual Lq sigma + flow) := by rw [hclean]
      _ ≤ HammingWeight (rxResidual Lq sigma) + HammingWeight flow :=
        HammingWeight_add_le _ _
      _ ≤ HammingWeight (rxResidual Lq sigma) +
          HammingWeight (rxLocalPart Lq sigma) := Nat.add_le_add_left hflow _
      _ = HammingWeight sigma :=
        RXSupportDecomposition.cq_residual_local_weight
          K.support_decomposition sigma
  · intro y hy
    rw [hclean]
    have hres : rxResidual Lq sigma y = 0 := by
      simp [rxResidual, outsideMaskWord, maskWord, hy]
    have hflow : flow y = 0 := by
      dsimp [flow]
      simp only [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro q hq
      exact K.support_decomposition.cqFlow_outside_q_sector q (f q) y hy
    change rxResidual Lq sigma y + flow y = 0
    rw [hres, hflow, add_zero]

theorem cx_local_ranges_of_syndrome
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (sigma : D.family.Syndrome i.succ) :
    ∀ x, restrictWordLinear (Lx.syndromeRegion x) (sigma : D.family.Cochain2 i.succ) ∈
      LinearMap.range (K.rx_local_complexes.cxDelta1 x) := by
  intro x
  rcases sigma.property with ⟨error, herror⟩
  refine ⟨restrictWordLinear (Lx.correctionRegion x) error, ?_⟩
  rw [← K.support_decomposition.cxDelta1_restriction_global x error, herror]

theorem cq_local_ranges_of_error
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hX : ∀ x, restrictWordLinear (Lx.correctionRegion x) error = 0) :
    ∀ q, restrictWordLinear (Lq.syndromeRegion q)
        (D.family.coboundary1 i.succ error) ∈
      LinearMap.range (K.rx_local_complexes.cqDelta1 q) := by
  intro q
  refine ⟨restrictWordLinear (Lq.correctionRegion q) error, ?_⟩
  exact (K.support_decomposition.cqDelta1_restriction_global q error hX).symm

/-!
The following adapters stop at the source-exact local-sector claim: they show
that every `C_x` restriction vanishes after adding a supported `δ⁰` term.  A
global identification of the remaining coordinates with `C_Q¹` is deliberately
left to the concrete M13 support partition.
-/

theorem cx_error_cleaning
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (x : X) (error : D.family.Cochain1 i.succ)
    (hcocycle : K.rx_local_complexes.cxDelta1 x
        (restrictWordLinear (Lx.correctionRegion x) error) = 0) :
    ∃ stabilizer : Word BDL26Field (X0 x),
      restrictWordLinear (Lx.correctionRegion x)
        (error + D.family.coboundary0 i.succ
          (K.support_decomposition.cxLift0 x stabilizer)) = 0 := by
  have hmem : restrictWordLinear (Lx.correctionRegion x) error ∈
      LinearMap.ker (K.rx_local_complexes.cxDelta1 x) := hcocycle
  rw [K.rx_local_cohomology.cx_h1_ker_eq_range x] at hmem
  rcases hmem with ⟨stabilizer, hstabilizer⟩
  refine ⟨stabilizer, ?_⟩
  rw [map_add, K.support_decomposition.cxDelta0_restriction, hstabilizer]
  ext j
  exact ZModModule.add_self _

theorem cx_error_cleaning_all
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hcocycle : ∀ x, K.rx_local_complexes.cxDelta1 x
        (restrictWordLinear (Lx.correctionRegion x) error) = 0) :
    ∃ stabilizers : ∀ x, Word BDL26Field (X0 x),
      ∀ x, restrictWordLinear (Lx.correctionRegion x)
        (error + D.family.coboundary0 i.succ
          (∑ y : X, K.support_decomposition.cxLift0 y (stabilizers y))) = 0 := by
  classical
  let stabilizers : ∀ x, Word BDL26Field (X0 x) := fun x =>
    Classical.choose (show ∃ s, K.rx_local_complexes.cxDelta0 x s =
      restrictWordLinear (Lx.correctionRegion x) error from by
      have hmem : restrictWordLinear (Lx.correctionRegion x) error ∈
          LinearMap.ker (K.rx_local_complexes.cxDelta1 x) := hcocycle x
      rw [K.rx_local_cohomology.cx_h1_ker_eq_range x] at hmem
      exact hmem)
  have hspec : ∀ x, K.rx_local_complexes.cxDelta0 x (stabilizers x) =
      restrictWordLinear (Lx.correctionRegion x) error := by
    intro x
    exact Classical.choose_spec (show ∃ s, K.rx_local_complexes.cxDelta0 x s =
      restrictWordLinear (Lx.correctionRegion x) error from by
      have hmem : restrictWordLinear (Lx.correctionRegion x) error ∈
          LinearMap.ker (K.rx_local_complexes.cxDelta1 x) := hcocycle x
      rw [K.rx_local_cohomology.cx_h1_ker_eq_range x] at hmem
      exact hmem)
  refine ⟨stabilizers, ?_⟩
  intro x
  rw [map_add, K.support_decomposition.cxDelta0_sum_decomposition,
    hspec]
  ext j
  exact ZModModule.add_self _

theorem cx_flow_zero_on_x_sector
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (f : ∀ x, Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x))) :
    ∀ y ∈ rxRegionUnion Lx,
      (∑ x : X, K.support_decomposition.cxFlow x (f x)) y = 0 := by
  intro y hy
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  exact K.support_decomposition.cxFlow_outside_x_sector x (f x) y hy

theorem cq_flow_zero_on_q_sector
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (f : ∀ q, Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q))) :
    ∀ y ∈ rxRegionUnion Lq,
      (∑ q : Q, K.support_decomposition.cqFlow q (f q)) y = 0 := by
  intro y hy
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  exact K.support_decomposition.cqFlow_outside_q_sector q (f q) y hy

end RXConstructionContractSlice

end MultiscaleDecoder
end Coding
end QEC
