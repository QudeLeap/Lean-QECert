import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.RXDifferentialMasks

/-!
# Actual RX incidence hulls as finite-path components

This internal diagnostic identifies the already-defined least hull with actual
Q--Z incidence paths. The graph here describes the differential-mask operator;
it does not redefine the marked decoding graph or assert history locality.
-/
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26RXIncidenceHullGrowth

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder

/-- Finite paths using a shared actual Z check. Reflexivity also covers Q
coordinates with no incident Z check. -/
inductive SharedZPath (P : TannerSquarePresentation) : P.Q → P.Q → Prop
  | refl (q : P.Q) : SharedZPath P q q
  | snoc {q r t : P.Q} (path : SharedZPath P q r) (z : P.Z)
      (left : P.qz r z = true) (right : P.qz t z = true) : SharedZPath P q t

theorem SharedZPath.trans {P : TannerSquarePresentation} {q r t : P.Q}
    (first : SharedZPath P q r) (second : SharedZPath P r t) : SharedZPath P q t := by
  induction second with
  | refl => exact first
  | snoc path z left right ih => exact .snoc ih z left right

theorem SharedZPath.symm {P : TannerSquarePresentation} {q r : P.Q}
    (path : SharedZPath P q r) : SharedZPath P r q := by
  induction path with
  | refl => exact .refl _
  | @snoc r t path z left right ih =>
      exact (SharedZPath.snoc (SharedZPath.refl (P := P) t) z right left).trans ih

variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

/-- A union of actual finite-path components meeting the seed. -/
def pathUnion (seed : Finset (state S i.val).presentation.Q) :
    Finset (state S i.val).presentation.Q :=
  Finset.univ.filter fun r => ∃ q ∈ seed, SharedZPath (state S i.val).presentation q r

theorem mem_pathUnion (seed : Finset (state S i.val).presentation.Q)
    (r : (state S i.val).presentation.Q) :
    r ∈ pathUnion S depth i seed ↔
      ∃ q ∈ seed, SharedZPath (state S i.val).presentation q r := by
  simp [pathUnion]

theorem path_mem_of_saturated (A : Finset (state S i.val).presentation.Q)
    (closed : IncidenceSaturated S depth i A)
    {q r : (state S i.val).presentation.Q} (hq : q ∈ A)
    (path : SharedZPath (state S i.val).presentation q r) : r ∈ A := by
  induction path with
  | refl => exact hq
  | snoc path z left right ih => exact closed _ ih _ z left right

theorem pathUnion_saturated (seed : Finset (state S i.val).presentation.Q) :
    IncidenceSaturated S depth i (pathUnion S depth i seed) := by
  intro q hq r z left right
  obtain ⟨a,ha,path⟩ := (mem_pathUnion S depth i seed q).mp hq
  exact (mem_pathUnion S depth i seed r).mpr ⟨a,ha,.snoc path z left right⟩

/-- Equality to the EXISTING least saturated hull, in both directions. -/
theorem incidenceHull_eq_pathUnion (seed : Finset (state S i.val).presentation.Q) :
    incidenceHull S depth i seed = pathUnion S depth i seed := by
  apply Finset.Subset.antisymm
  · apply incidenceHull_minimal S depth i seed
    · intro q hq
      exact (mem_pathUnion S depth i seed q).mpr ⟨q,hq,.refl q⟩
    · exact pathUnion_saturated S depth i seed
  · intro r hr
    obtain ⟨q,hq,path⟩ := (mem_pathUnion S depth i seed r).mp hr
    exact path_mem_of_saturated S depth i _ (incidenceHull_saturated S depth i seed)
      (subset_incidenceHull S depth i seed hq) path

theorem mem_incidenceHull_iff_path (seed : Finset (state S i.val).presentation.Q)
    (r : (state S i.val).presentation.Q) :
    r ∈ incidenceHull S depth i seed ↔
      ∃ q ∈ seed, SharedZPath (state S i.val).presentation q r := by
  rw [incidenceHull_eq_pathUnion]
  exact mem_pathUnion S depth i seed r

@[simp] theorem incidenceHull_empty :
    incidenceHull S depth i ∅ = ∅ := by
  apply Finset.ext
  intro q
  constructor
  · intro hq
    obtain ⟨a,ha,_⟩ := (mem_incidenceHull_iff_path S depth i ∅ q).mp hq
    simpa using ha
  · intro hq
    exact False.elim (by simpa using hq)

/-- Every point in a seed component is forced into ANY all-word commuting pair. -/
theorem commuting_pair_contains_paths (h : i.val % 2 = 0)
    (seed A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) (hseed : seed ⊆ A)
    (commutes : ∀ w, MultiscaleDecoder.maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (MultiscaleDecoder.maskWord A w))
    {q r : (state S i.val).presentation.Q} (hq : q ∈ seed)
    (path : SharedZPath (state S i.val).presentation q r) : r ∈ A := by
  exact (incidenceHull_le_every_commuting_pair S depth i h seed A B hseed commutes).1
    ((mem_incidenceHull_iff_path S depth i seed r).mpr ⟨q,hq,path⟩)

/-- All five seed Q coordinates join through the literal central seed Q4. -/
theorem base_shared_with_central (q : BaseQubit) :
    ∃ z : BaseZ, baseTannerSquarePresentation.qz q z = true ∧
      baseTannerSquarePresentation.qz (4 : BaseQubit) z = true := by
  have incident (a : BaseQubit) (z : BaseZ) (h : baseBoundary2Matrix a z ≠ 0) :
      baseTannerSquarePresentation.qz a z = true := by
    change decide (baseBoundary2Matrix a z ≠ 0) = true
    rw [decide_eq_true_eq]
    exact h
  fin_cases q
  · exact ⟨0,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩
  · exact ⟨1,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩
  · exact ⟨0,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩
  · exact ⟨1,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩
  · exact ⟨0,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩

theorem base_path (q r : BaseQubit) : SharedZPath baseTannerSquarePresentation q r := by
  obtain ⟨z,hq,hcenter⟩ := base_shared_with_central q
  obtain ⟨w,hr,hcenter'⟩ := base_shared_with_central r
  exact SharedZPath.snoc
    (SharedZPath.snoc (SharedZPath.refl (P := baseTannerSquarePresentation) q) z hq hcenter)
    w hcenter' hr

theorem base_nonempty_hull (seed : Finset BaseQubit) (hne : seed.Nonempty)
    (hd : 0 < depth) : incidenceHull S depth ⟨0,hd⟩ seed = Finset.univ := by
  obtain ⟨q,hq⟩ := hne
  apply Finset.eq_univ_of_forall
  intro r
  exact (mem_incidenceHull_iff_path S depth ⟨0,hd⟩ seed r).mpr ⟨q,hq,base_path q r⟩

theorem base_nonempty_hull_card (seed : Finset BaseQubit) (hne : seed.Nonempty)
    (hd : 0 < depth) : (incidenceHull S depth ⟨0,hd⟩ seed).card = 5 := by
  rw [base_nonempty_hull S depth seed hne hd]
  exact Finset.card_univ.trans baseQubit_card

end QEC.Coding.BDL26RXIncidenceHullGrowth
end
