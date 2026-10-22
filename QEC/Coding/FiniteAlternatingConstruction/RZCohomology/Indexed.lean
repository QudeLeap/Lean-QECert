import QEC.Coding.FiniteAlternatingConstruction.RZCohomology.Equivalence
import QEC.Coding.FiniteAlternatingConstruction.IndexedDecoder

/-!
# RZ H¹ equivalence on actual odd recursive steps

All primitive admissibility and regularity proofs come from the actual state.
The representative is the existing parity-selected nextMap1/stepMap1.
-/

namespace QEC.Coding.BDL26RZCohomology

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical

universe u

private theorem transported_heq {α β : Sort u} (h : α = β) (v : β) :
    HEq (Eq.mpr h v) v := by
  cases h
  rfl

private theorem transport_word_map_apply
    (P : TannerSquarePresentation) (D E : ConstructionState) (h : D = E)
    (f : Word Field P.Q →ₗ[Field] Word Field E.presentation.Q) (v : Word Field P.Q) :
    (Eq.mpr (congrArg (fun T : ConstructionState =>
      Word Field P.Q →ₗ[Field] Word Field T.presentation.Q) h) f) v =
    Eq.mpr (congrArg (fun T : ConstructionState => Word Field T.presentation.Q) h) (f v) := by
  cases h
  rfl

private theorem transport_forward_mk
    (P : TannerSquarePresentation) (D E : ConstructionState) (h : D = E)
    (f : Word Field P.Q →ₗ[Field] Word Field E.presentation.Q)
    (g : Cocycle P →ₗ[Field] Cocycle E.presentation)
    (hg : ∀ v, (g v).val = f v.val)
    (e : H1 P ≃ₗ[Field] H1 E.presentation)
    (he : ∀ v, e (classOf P v) = classOf E.presentation (g v))
    (G : Cocycle P →ₗ[Field] Cocycle D.presentation)
    (hG : ∀ v, (G v).val =
      Eq.mpr (congrArg (fun T : ConstructionState => Word Field T.presentation.Q) h) (f v.val))
    (v : Cocycle P) :
    (Eq.mpr (congrArg (fun T : ConstructionState => H1 P ≃ₗ[Field] H1 T.presentation) h) e)
      (classOf P v) = classOf D.presentation (G v) := by
  cases h
  have hv : G v = g v := Subtype.ext ((hG v).trans (hg v).symm)
  rw [hv]
  exact he v

private theorem transport_backward_mk
    (P : TannerSquarePresentation) (D E : ConstructionState) (h : D = E)
    (e : H1 P ≃ₗ[Field] H1 E.presentation)
    (g : Cocycle E.presentation →ₗ[Field] Cocycle P)
    (he : ∀ w, e.symm (classOf E.presentation w) = classOf P (g w))
    (w : Cocycle D.presentation) :
    (Eq.mpr (congrArg (fun T : ConstructionState => H1 P ≃ₗ[Field] H1 T.presentation) h) e).symm
      (classOf D.presentation w) =
    classOf P ((Eq.mpr (congrArg (fun T : ConstructionState =>
      Cocycle T.presentation →ₗ[Field] Cocycle P) h) g) w) := by
  cases h
  exact he w


/-- The genuine next cochain map preserves the actual cocycle submodule. -/
noncomputable def nextCocycle (S : OddScale) (n : Nat) (C : ConstructionState) :
    Cocycle C.presentation →ₗ[Field] Cocycle (nextState S n C).presentation where
  toFun v := ⟨nextMap1 S n C v.1, by
    apply (mem_cocycle_iff _ _).mpr
    have hc := LinearMap.congr_fun (nextMap_commutes1 S n C) v.1
    change tannerCoboundary1 (nextState S n C).presentation (nextMap1 S n C v.1) =
      nextMap2 S n C (tannerCoboundary1 C.presentation v.1) at hc
    rw [(mem_cocycle_iff _ _).mp v.2, map_zero] at hc
    exact hc⟩
  map_add' _ _ := Subtype.ext ((nextMap1 S n C).map_add _ _)
  map_smul' _ _ := Subtype.ext ((nextMap1 S n C).map_smul _ _)

/-- Transport the actual RZ equivalence along the defining odd parity branch. -/
noncomputable def nextEquiv (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) :
    H1 C.presentation ≃ₗ[Field] H1 (nextState S n C).presentation := by
  exact Eq.mpr (congrArg (fun T : ConstructionState =>
    H1 C.presentation ≃ₗ[Field] H1 T.presentation)
    (show nextState S n C = rzState S C from if_neg h))
    (equiv C.presentation C.admissible C.regular S)

/-- The inverse cocycle representative on that very same transported carrier. -/
noncomputable def nextBackwardCocycle (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) :
    Cocycle (nextState S n C).presentation →ₗ[Field] Cocycle C.presentation := by
  exact Eq.mpr (congrArg (fun T : ConstructionState =>
    Cocycle T.presentation →ₗ[Field] Cocycle C.presentation)
    (show nextState S n C = rzState S C from if_neg h))
    (backwardCocycle C.presentation C.admissible S)

/-- The inverse remains the literal Q-parity map, up to the defining carrier
transport. This is map equality evidence, not an assumed H¹ isomorphism. -/
theorem nextBackwardCocycle_heq (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) :
    HEq (nextBackwardCocycle S n C h) (backwardCocycle C.presentation C.admissible S) := by
  exact transported_heq _ _

theorem nextEquiv_mk (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) (v : Cocycle C.presentation) :
    nextEquiv S n C h (classOf C.presentation v) =
      classOf (nextState S n C).presentation (nextCocycle S n C v) := by
  apply transport_forward_mk C.presentation (nextState S n C) (rzState S C)
    (show nextState S n C = rzState S C from if_neg h)
    (map1Coord C.presentation C.admissible S)
    (forwardCocycle C.presentation C.admissible S) (fun _ => rfl)
    (equiv C.presentation C.admissible C.regular S)
    (equiv_mk C.presentation C.admissible C.regular S) (nextCocycle S n C) _ v
  intro a
  change nextMap1 S n C a.val = _
  simpa only [nextMap1, dif_neg h] using
    transport_word_map_apply C.presentation (nextState S n C) (rzState S C)
      (show nextState S n C = rzState S C from if_neg h)
      (map1Coord C.presentation C.admissible S) a.val

theorem nextEquiv_symm_mk (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) (w : Cocycle (nextState S n C).presentation) :
    (nextEquiv S n C h).symm (classOf (nextState S n C).presentation w) =
      classOf C.presentation (nextBackwardCocycle S n C h w) := by
  exact transport_backward_mk C.presentation (nextState S n C) (rzState S C)
    (show nextState S n C = rzState S C from if_neg h)
    (equiv C.presentation C.admissible C.regular S)
    (backwardCocycle C.presentation C.admissible S)
    (equiv_symm_mk C.presentation C.admissible C.regular S) w

private theorem odd_lower (k : Nat) : ¬ (2 * k + 1) % 2 = 0 := by omega

/-- Every actual odd recursive step induces the constructed RZ H¹ equivalence. -/
noncomputable def oddEquiv (S : OddScale) (k : Nat) :
    H1 (state S (2 * k + 1)).presentation ≃ₗ[Field]
      H1 (state S (2 * k + 2)).presentation :=
  nextEquiv S (2 * k + 1) (state S (2 * k + 1)) (odd_lower k)

noncomputable def oddCocycle (S : OddScale) (k : Nat) :
    Cocycle (state S (2 * k + 1)).presentation →ₗ[Field]
      Cocycle (state S (2 * k + 2)).presentation :=
  nextCocycle S (2 * k + 1) (state S (2 * k + 1))

noncomputable def oddBackwardCocycle (S : OddScale) (k : Nat) :
    Cocycle (state S (2 * k + 2)).presentation →ₗ[Field]
      Cocycle (state S (2 * k + 1)).presentation :=
  nextBackwardCocycle S (2 * k + 1) (state S (2 * k + 1)) (odd_lower k)

/-- The actual forward cocycle word is literally the existing selected map. -/
theorem oddCocycle_value (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k + 1)).presentation) :
    (oddCocycle S k v).1 = stepMap1 S (2 * k + 1) v.1 := rfl

/-- Representative formula for every cocycle at every actual odd step. -/
theorem oddEquiv_mk (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k + 1)).presentation) :
    oddEquiv S k (classOf (state S (2 * k + 1)).presentation v) =
      classOf (state S (2 * k + 2)).presentation (oddCocycle S k v) :=
  nextEquiv_mk S (2 * k + 1) (state S (2 * k + 1)) (odd_lower k) v

/-- Backward representative formula on the actual upper recursive state. -/
theorem oddEquiv_symm_mk (S : OddScale) (k : Nat)
    (w : Cocycle (state S (2 * k + 2)).presentation) :
    (oddEquiv S k).symm (classOf (state S (2 * k + 2)).presentation w) =
      classOf (state S (2 * k + 1)).presentation (oddBackwardCocycle S k w) :=
  nextEquiv_symm_mk S (2 * k + 1) (state S (2 * k + 1)) (odd_lower k) w

end QEC.Coding.BDL26RZCohomology
