import QEC.Coding.FiniteAlternatingConstruction.OwnerParentObstruction

/-!
# Concrete RZ block parity and root lifts

The actual Sigma-labelled Z blocks recover the input of the selected degree-two
map by parity. Its restriction to a block is the distinguished-root lift, so
the corresponding local residual vanishes. This does not construct a decoder
adapter, choose a correction, or assert any history/component property.
-/

namespace QEC.Coding.BDL26RZConcreteParity

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

/-- The actual Z block, selected by the first Sigma coordinate. -/
noncomputable def blockRegion (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : Finset (RZZ P S) :=
  fiberRegion (fun t : RZZ P S => t.1) z

/-- Restriction to a Z block, extended by zero in the original carrier. -/
noncomputable def blockPart (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : Word BDL26Field (RZZ P S) →ₗ[BDL26Field] Word BDL26Field (RZZ P S) :=
  fiberPart (fun t : RZZ P S => t.1) z

/-- Parity over the actual vertices in one Z block. -/
noncomputable def blockParity (P : TannerSquarePresentation) (S : OddScale)
    (r : Word BDL26Field (RZZ P S)) : Word BDL26Field P.Z :=
  fun z => ∑ v : ZDoubleCylinderVertex P z S, r ⟨z,v⟩

/-- The lift uses the existing selected map and its distinguished root. -/
noncomputable def rootLift (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (b : BDL26Field) : Word BDL26Field (RZZ P S) :=
  map2Coord P A S (Pi.single z b)

theorem blockRegion_disjoint (P : TannerSquarePresentation) (S : OddScale)
    {z w : P.Z} (h : z ≠ w) : Disjoint (blockRegion P S z) (blockRegion P S w) :=
  fiberRegion_disjoint (fun t : RZZ P S => t.1) h

theorem blockParity_eq_region_sum (P : TannerSquarePresentation) (S : OddScale)
    (r : Word BDL26Field (RZZ P S)) (z : P.Z) :
    blockParity P S r z = ∑ t ∈ blockRegion P S z, r t := by
  simp only [blockRegion, fiberRegion, Finset.sum_filter, Fintype.sum_sigma]
  symm
  rw [Finset.sum_eq_single z]
  · simp only [blockParity, ite_true]
    refine Finset.sum_congr (by ext v; simp only [Finset.mem_univ]) ?_
    intro v _
    rfl
  · intro w _ hw
    simp [hw]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem rootLift_apply (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z w : P.Z) (b : BDL26Field) (v : ZDoubleCylinderVertex P w S) :
    rootLift P A S z b ⟨w,v⟩ =
      if v = rzMap1ZRoot P A w S then (Pi.single z b : Word BDL26Field P.Z) w else 0 :=
  rzMap2_apply P A S (Pi.single z b) w v

theorem rootLift_support (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (b : BDL26Field) :
    hammingSupport (rootLift P A S z b) ⊆ blockRegion P S z := by
  intro t ht
  rcases t with ⟨w,v⟩
  by_cases h : w = z
  · simp [blockRegion, fiberRegion, h]
  · have hz : rootLift P A S z b ⟨w,v⟩ = 0 := by
      rw [rootLift_apply]
      simp [Pi.single_apply, h, Ne.symm h]
    simpa [hammingSupport, hz] using ht

/-- Block parity is a left inverse of the actual RZ degree-two map. -/
theorem blockParity_map2 (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (s : Word BDL26Field P.Z) :
    blockParity P S (map2Coord P A S s) = s := by
  funext z
  change (∑ v : ZDoubleCylinderVertex P z S, map2Coord P A S s ⟨z,v⟩) = s z
  rw [Finset.sum_eq_single (rzMap1ZRoot P A z S)]
  · simp only [rzMap2_apply, ite_true]
  · intro v _ hv
    simp only [rzMap2_apply, if_neg hv]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem map2_injective (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : Function.Injective (map2Coord P A S) := by
  intro s t h
  have hp := congrArg (blockParity P S) h
  simpa only [blockParity_map2] using hp

theorem blockPart_map2 (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (s : Word BDL26Field P.Z) (z : P.Z) :
    blockPart P S z (map2Coord P A S s) = rootLift P A S z (s z) := by
  funext t
  rcases t with ⟨w,v⟩
  by_cases h : w = z
  · subst w
    simp [blockPart, fiberPart_apply, rootLift, rzMap2_apply]
  · simp [blockPart, fiberPart_apply, rootLift, rzMap2_apply,
      Pi.single_apply, h, Ne.symm h]

theorem sum_rootLift (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (s : Word BDL26Field P.Z) :
    (∑ z : P.Z, rootLift P A S z (s z)) = map2Coord P A S s := by
  simp_rw [← blockPart_map2]
  exact sum_fiberPart (fun t : RZZ P S => t.1) (map2Coord P A S s)

/-- The concrete residual vanishes; a chosen correction may still be a cycle. -/
theorem localResidual_map2_eq_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (s : Word BDL26Field P.Z)
    (z : P.Z) :
    blockPart P S z (map2Coord P A S s) +
      rootLift P A S z (blockParity P S (map2Coord P A S s) z) = 0 := by
  rw [blockParity_map2, blockPart_map2]
  funext t
  exact CharTwo.add_self_eq_zero (rootLift P A S z (s z) t)

end QEC.Coding.BDL26RZConcreteParity
