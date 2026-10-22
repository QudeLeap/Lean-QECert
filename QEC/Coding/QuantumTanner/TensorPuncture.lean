import QEC.Coding.QuantumTanner.Goodness

/-!
# Rectangular puncturing of tensor codes

Every word of the tensor product of the punctured local codes lifts to an
actual original tensor word. This is the attainability step used in
[LZ22, proof of Theorem thm:main] after Proposition prop:tensor.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe u v

variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

/-- Restrict both coordinates to the retained rectangle. -/
def tensorPunctureMap (removedA : Finset A) (removedB : Finset B) :
    Word F (A × B) →ₗ[F] Word F (KeptCoordinate removedA × KeptCoordinate removedB) where
  toFun x ab := x (ab.1.1, ab.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A product of two actual local-code words satisfies both tensor constraints. -/
theorem pureWord_mem_tensorCode
    (CA : LinearCode F A) (CB : LinearCode F B) (a : Word F A) (b : Word F B)
    (ha : a ∈ CA.carrier) (hb : b ∈ CB.carrier) :
    (fun ab : A × B => a ab.1 * b ab.2) ∈ (tensorCode CA CB).carrier := by
  constructor
  · intro j
    change (fun i => a i * b j) ∈ CA.carrier
    rw [show (fun i => a i * b j) = (b j) • a by
      ext i
      simp [mul_comm]]
    exact CA.carrier.smul_mem (b j) ha
  · intro i
    change (fun j => a i * b j) ∈ CB.carrier
    rw [show (fun j => a i * b j) = (a i) • b by
      ext j
      simp]
    exact CB.carrier.smul_mem (a i) hb

/-- Rectangular puncturing sends original tensor words to punctured tensor words. -/
theorem tensorPunctureMap_mem
    (CA : LinearCode F A) (CB : LinearCode F B)
    (removedA : Finset A) (removedB : Finset B)
    (x : Word F (A × B)) (hx : x ∈ (tensorCode CA CB).carrier) :
    tensorPunctureMap removedA removedB x ∈
      (tensorCode (puncturedCode CA removedA) (puncturedCode CB removedB)).carrier := by
  constructor
  · intro b
    apply (mem_puncturedCode CA removedA _).mpr
    exact ⟨columnRestriction b.1 x, hx.1 b.1, rfl⟩
  · intro a
    apply (mem_puncturedCode CB removedB _).mpr
    exact ⟨rowRestriction a.1 x, hx.2 a.1, rfl⟩

/-- Tensor puncturing is onto the tensor product of the actual punctured codes;
no lifting witness is included among the assumptions. -/
theorem exists_tensorCode_lift_punctured
    (CA : LinearCode F A) (CB : LinearCode F B)
    (removedA : Finset A) (removedB : Finset B)
    (x : Word F (KeptCoordinate removedA × KeptCoordinate removedB))
    (hx : x ∈
      (tensorCode (puncturedCode CA removedA) (puncturedCode CB removedB)).carrier) :
    ∃ z : Word F (A × B), z ∈ (tensorCode CA CB).carrier ∧
      tensorPunctureMap removedA removedB z = x := by
  apply tensorCode_induction (puncturedCode CA removedA) (puncturedCode CB removedB)
    ?_ ?_ ?_ x hx
  · exact ⟨0, (tensorCode CA CB).carrier.zero_mem, map_zero _⟩
  · intro y z hy hz
    obtain ⟨Y, hY, hYeq⟩ := hy
    obtain ⟨Z, hZ, hZeq⟩ := hz
    exact ⟨Y + Z, (tensorCode CA CB).carrier.add_mem hY hZ,
      by rw [map_add, hYeq, hZeq]⟩
  · intro a ha b hb
    obtain ⟨aFull, haFull, haEq⟩ := (mem_puncturedCode CA removedA a).mp ha
    obtain ⟨bFull, hbFull, hbEq⟩ := (mem_puncturedCode CB removedB b).mp hb
    refine ⟨(fun ab => aFull ab.1 * bFull ab.2),
      pureWord_mem_tensorCode CA CB aFull bFull haFull hbFull, ?_⟩
    ext ab
    exact congrArg₂ (· * ·) (congrFun haEq ab.1) (congrFun hbEq ab.2)

/-- The deleted rectangle costs at most one full row or column per puncture.
Overlaps are counted only once on the left and may be counted twice in the bound. -/
theorem hammingWeight_tensorPuncture_loss_le [DecidableEq F]
    (removedA : Finset A) (removedB : Finset B) (x : Word F (A × B)) :
    HammingWeight x ≤ HammingWeight (tensorPunctureMap removedA removedB x) +
      removedA.card * Fintype.card B + Fintype.card A * removedB.card := by
  let deleted : Finset (A × B) :=
    (removedA.product Finset.univ) ∪ (Finset.univ.product removedB)
  let keep : KeptCoordinate removedA × KeptCoordinate removedB → A × B :=
    fun ab => (ab.1.1, ab.2.1)
  have hInjective : Function.Injective keep := by
    intro a b hab
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hab))
      (Subtype.ext (congrArg Prod.snd hab))
  have hImage : (hammingSupport (tensorPunctureMap removedA removedB x)).image keep =
      hammingSupport x \ deleted := by
    ext ab
    constructor
    · intro h
      obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp h
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hij).2⟩, ?_⟩
      simp [deleted, keep, ij.1.2, ij.2.2]
    · intro h
      obtain ⟨hab, hKept⟩ := Finset.mem_sdiff.mp h
      have hk : ab.1 ∉ removedA ∧ ab.2 ∉ removedB := by
        simpa [deleted] using hKept
      exact Finset.mem_image.mpr ⟨(⟨ab.1, hk.1⟩, ⟨ab.2, hk.2⟩),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hab).2⟩, rfl⟩
  have hCard := congrArg Finset.card hImage
  rw [Finset.card_image_of_injective _ hInjective] at hCard
  have hPartition := Finset.card_sdiff_add_card_inter (hammingSupport x) deleted
  have hInter : (hammingSupport x ∩ deleted).card ≤ deleted.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hDeleted : deleted.card ≤
      removedA.card * Fintype.card B + Fintype.card A * removedB.card := by
    calc
      deleted.card ≤ (removedA.product (Finset.univ : Finset B)).card +
          ((Finset.univ : Finset A).product removedB).card := Finset.card_union_le _ _
      _ = _ := by simp only [Finset.product_eq_sprod, Finset.card_product,
        Finset.card_univ]
  change (hammingSupport x).card ≤
    (hammingSupport (tensorPunctureMap removedA removedB x)).card + _ + _
  omega

/-- Equal-size coordinate sets can absorb both exceptional sets without
increasing the larger exceptional-set size. This supplies matching punctures
for the resistance hypothesis, rather than assuming matching bad sets. -/
theorem exists_balanced_punctures
    (badA : Finset A) (badB : Finset B) (p : Nat)
    (hCard : Fintype.card A = Fintype.card B)
    (hA : badA.card ≤ p) (hB : badB.card ≤ p) (hp : p ≤ Fintype.card A) :
    ∃ removedA : Finset A, ∃ removedB : Finset B,
      badA ⊆ removedA ∧ badB ⊆ removedB ∧
      removedA.card = removedB.card ∧ removedA.card ≤ p := by
  let m := max badA.card badB.card
  have hm : m ≤ p := max_le hA hB
  obtain ⟨removedA, hContainsA, hSizeA⟩ :=
    Finset.exists_superset_card_eq (le_max_left badA.card badB.card) (hm.trans hp)
  obtain ⟨removedB, hContainsB, hSizeB⟩ :=
    Finset.exists_superset_card_eq (le_max_right badA.card badB.card)
      (hm.trans (hp.trans_eq hCard))
  exact ⟨removedA, removedB, hContainsA, hContainsB,
    hSizeA.trans hSizeB.symm, hSizeA.le.trans hm⟩

/-- Deleting coordinates loses at most their cardinality in Hamming weight. -/
theorem hammingWeight_puncture_loss_le [DecidableEq F]
    (removed : Finset A) (x : Word F A) :
    HammingWeight x ≤ HammingWeight (punctureMap removed x) + removed.card := by
  have hImage : (hammingSupport (punctureMap removed x)).image Subtype.val =
      hammingSupport x \ removed := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, i.2⟩
    · intro ha
      obtain ⟨ha, hNot⟩ := Finset.mem_sdiff.mp ha
      exact Finset.mem_image.mpr ⟨⟨a, hNot⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩, rfl⟩
  have hCard := congrArg Finset.card hImage
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hCard
  have hPartition := Finset.card_sdiff_add_card_inter (hammingSupport x) removed
  have hInter := Finset.card_le_card (Finset.inter_subset_right :
    hammingSupport x ∩ removed ⊆ removed)
  change (hammingSupport x).card ≤ (hammingSupport (punctureMap removed x)).card + _
  omega

/-- The actual punctured code retains the expected minimum-distance lower bound. -/
theorem hasMinimumDistanceAtLeast_punctured [DecidableEq F]
    (C : LinearCode F A) (d : Nat) (hC : HasMinimumDistanceAtLeast C d)
    (removed : Finset A) :
    HasMinimumDistanceAtLeast (puncturedCode C removed) (d - removed.card) := by
  intro y hy hy0
  obtain ⟨x, hx, rfl⟩ := (mem_puncturedCode C removed y).mp hy
  have hx0 : x ≠ 0 := by
    intro h
    exact hy0 (by rw [h, map_zero])
  have hDistance := hC x hx hx0
  have hLoss := hammingWeight_puncture_loss_le removed x
  omega

/-- Fewer deletions than the actual distance preserve a nonzero word and hence
an attained punctured minimum. No punctured-distance witness is postulated. -/
theorem exists_punctured_minimumDistance [DecidableEq F]
    (C : LinearCode F A) (d : Nat) (hC : MinimumDistance C d)
    (removed : Finset A) (hRemoved : removed.card < d) :
    ∃ d', MinimumDistance (puncturedCode C removed) d' ∧ d - removed.card ≤ d' := by
  obtain ⟨x, hx, hx0, hxWeight, hLeast⟩ := hC
  have hPunctured0 : punctureMap removed x ≠ 0 := by
    intro hZero
    have hLoss := hammingWeight_puncture_loss_le removed x
    rw [hZero, hxWeight] at hLoss
    have hImpossible : d ≤ removed.card := by
      simpa [HammingWeight, hammingSupport] using hLoss
    omega
  obtain ⟨d', hd'⟩ := exists_minimumDistance_of_exists_nonzero (puncturedCode C removed)
    ⟨punctureMap removed x, (mem_puncturedCode C removed _).mpr ⟨x, hx, rfl⟩, hPunctured0⟩
  refine ⟨d', hd', ?_⟩
  obtain ⟨y, hy, hy0, hyWeight, hLeast'⟩ := hd'
  have hBound := hasMinimumDistanceAtLeast_punctured C d hLeast removed y hy hy0
  rwa [hyWeight] at hBound

end QEC.Coding.QuantumTanner
