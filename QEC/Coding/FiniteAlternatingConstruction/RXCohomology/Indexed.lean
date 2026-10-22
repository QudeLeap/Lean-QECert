import QEC.Coding.FiniteAlternatingConstruction.RXCohomology.Equivalence
import QEC.Coding.FiniteAlternatingConstruction.IndexedDecoder

/-!
# RX H¹ equivalence on actual even recursive steps

All primitive admissibility and regularity proofs come from the actual state.
The representative is the existing literal RX nextMap1/stepMap1.
-/

namespace QEC.Coding.BDL26RXCohomology

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

/-- The genuine next cochain map preserves the actual cocycle submodule. -/
noncomputable def nextCocycle (S : OddScale) (n : Nat) (C : ConstructionState) :
    Cocycle C.presentation →ₗ[Field] Cocycle (nextState S n C).presentation where
  toFun v := ⟨nextMap1 S n C v.1, by
    apply (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
    have hc := LinearMap.congr_fun (nextMap_commutes1 S n C) v.1
    change tannerCoboundary1 (nextState S n C).presentation (nextMap1 S n C v.1) =
      nextMap2 S n C (tannerCoboundary1 C.presentation v.1) at hc
    rw [(BDL26RZCohomology.mem_cocycle_iff _ _).mp v.2, map_zero] at hc
    exact hc⟩
  map_add' _ _ := Subtype.ext ((nextMap1 S n C).map_add _ _)
  map_smul' _ _ := Subtype.ext ((nextMap1 S n C).map_smul _ _)

/-- Transport the actual RX equivalence along the defining even parity branch. -/
noncomputable def nextEquiv (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : n % 2 = 0) :
    H1 C.presentation ≃ₗ[Field] H1 (nextState S n C).presentation := by
  exact Eq.mpr (congrArg (fun T : ConstructionState =>
    H1 C.presentation ≃ₗ[Field] H1 T.presentation)
    (show nextState S n C = rxState S C from if_pos h))
    (equiv C.presentation C.admissible C.regular S)

theorem nextEquiv_mk (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : n % 2 = 0) (v : Cocycle C.presentation) :
    nextEquiv S n C h (classOf C.presentation v) =
      classOf (nextState S n C).presentation (nextCocycle S n C v) := by
  apply transport_forward_mk C.presentation (nextState S n C) (rxState S C)
    (show nextState S n C = rxState S C from if_pos h)
    (rxMap1Coord C.presentation S)
    (forwardCocycle C.presentation C.admissible C.regular S) (fun _ => rfl)
    (equiv C.presentation C.admissible C.regular S)
    (equiv_mk C.presentation C.admissible C.regular S) (nextCocycle S n C) _ v
  intro a
  change nextMap1 S n C a.val = _
  simpa only [nextMap1, dif_pos h] using
    transport_word_map_apply C.presentation (nextState S n C) (rxState S C)
      (show nextState S n C = rxState S C from if_pos h)
      (rxMap1Coord C.presentation S) a.val

private theorem even_lower (k : Nat) : (2 * k) % 2 = 0 := by omega

/-- Every actual even recursive step induces the constructed RX H¹ equivalence. -/
noncomputable def evenEquiv (S : OddScale) (k : Nat) :
    H1 (state S (2 * k)).presentation ≃ₗ[Field]
      H1 (state S (2 * k + 1)).presentation :=
  nextEquiv S (2 * k) (state S (2 * k)) (even_lower k)

noncomputable def evenCocycle (S : OddScale) (k : Nat) :
    Cocycle (state S (2 * k)).presentation →ₗ[Field]
      Cocycle (state S (2 * k + 1)).presentation :=
  nextCocycle S (2 * k) (state S (2 * k))

/-- The actual forward cocycle word is literally the existing selected map. -/
theorem evenCocycle_value (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k)).presentation) :
    (evenCocycle S k v).1 = stepMap1 S (2 * k) v.1 := rfl

/-- Representative formula for every cocycle at every actual even step. -/
theorem evenEquiv_mk (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k)).presentation) :
    evenEquiv S k (classOf (state S (2 * k)).presentation v) =
      classOf (state S (2 * k + 1)).presentation (evenCocycle S k v) :=
  nextEquiv_mk S (2 * k) (state S (2 * k)) (even_lower k) v

open BDL26IndexedDecoder MultiscaleDecoder

/-- H¹ equivalence on the actual indexed-family edge at every even lower index. -/
noncomputable def indexedEquiv (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) :
    ((indexedFamily S depth).complex i.castSucc).middleCohomology ≃ₗ[Field]
      ((indexedFamily S depth).complex i.succ).middleCohomology :=
  nextEquiv S i.val (state S i.val) h

noncomputable def indexedCocycle (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier →ₗ[Field]
      ((indexedFamily S depth).complex i.succ).middleCocycleCode.carrier :=
  nextCocycle S i.val (state S i.val)

/-- Complete representative action is exactly the actual selected indexed map. -/
theorem indexedCocycle_value (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (v : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    (indexedCocycle S depth i v).1 =
      ((indexedDecoderData S depth).selectedMap i).map1 v.1 := by
  rw [selectedMap_eq]
  rfl

theorem indexedEquiv_mk (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0)
    (v : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    indexedEquiv S depth i h
      (((indexedFamily S depth).complex i.castSucc).middleCoboundaryInCocycles.mkQ v) =
      ((indexedFamily S depth).complex i.succ).middleCoboundaryInCocycles.mkQ
        (indexedCocycle S depth i v) := nextEquiv_mk S i.val (state S i.val) h v

end QEC.Coding.BDL26RXCohomology
