import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeTriangleColors
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Events

/-!
Project-derived internal/API primitive-key event closure, pinned BDL26 paper.tex
1409–1424. Speculative stacked source over audited PR1608 H7aec; no kernel,
recursive embedding, execution-law or expected-time completion is claimed.
-/
namespace QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
def KeyEligible (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (s : Finset (Triangle P)) : Prop :=
  s.card = 4 ∧
    (∀ a ∈ s, ∀ b ∈ s, BDL26NativeTriangleColors.policyColor P key a = BDL26NativeTriangleColors.policyColor P key b) ∧
    ∀ a ∈ s, ∀ b ∈ s, dist (oldAnchor P J a) (oldAnchor P J b) ≤ radius

abbrev KeyEvent (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ) :=
  {s : Finset (Triangle P) // KeyEligible P key hk J radius s}

noncomputable instance keyEventFintype (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) : Fintype (KeyEvent P key hk J radius) := Fintype.ofFinite _

theorem keyEvent_nonempty (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) : e.val.Nonempty := by
  apply Finset.card_pos.mp
  rw [e.property.1]
  norm_num

/-- The least enumerated label gives a deterministic anchor, independent of samples. -/
noncomputable def keyAnchor (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) (e : KeyEvent P key hk J radius) : Triangle P := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' key hk
  exact e.val.min' (keyEvent_nonempty P key hk J radius e)

theorem keyAnchor_mem (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) : keyAnchor P key hk J radius e ∈ e.val := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' key hk
  exact Finset.min'_mem e.val (keyEvent_nonempty P key hk J radius e)

/-- Only the actual domain vertices are resampled. -/
noncomputable def keySupport (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) (e : KeyEvent P key hk J radius) : Finset (Vertex P) := by
  classical
  exact e.val.biUnion (triangleSupport P)

theorem keySupport_card_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) (e : KeyEvent P key hk J radius) : (keySupport P key hk J radius e).card ≤ 12 := by
  classical
  calc
    _ ≤ ∑ a ∈ e.val, (triangleSupport P a).card := Finset.card_biUnion_le
    _ = e.val.card*3 := by simp [triangleSupport_card]
    _ = 12 := by norm_num [e.property.1]

/-- Each local triangle coordinate refers to the corresponding variable in the union. -/
def keyVertex (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) (a : e.val) (i : Fin 3) : keySupport P key hk J radius e :=
  ⟨triangleVertex P a.val i, by
    classical
    exact Finset.mem_biUnion.mpr ⟨a.val,a.property,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩⟩

theorem keyEvent_card_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ) :
    Fintype.card (KeyEvent P key hk J radius) ≤ Fintype.card (Triangle P)^4 := by
  classical
  let encode : KeyEvent P key hk J radius → ↥((Finset.univ : Finset (Triangle P)).powersetCard 4) :=
    fun e => ⟨e.val,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,e.property.1⟩⟩
  have hinj : Function.Injective encode := by
    intro e f h
    have he := congrArg (fun s : ↥((Finset.univ : Finset (Triangle P)).powersetCard 4) => s.val) h
    exact Subtype.ext he
  have hc := Fintype.card_le_of_injective encode hinj
  have hc' : Fintype.card (KeyEvent P key hk J radius) ≤ (Fintype.card (Triangle P)).choose 4 := by
    simpa only [Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ] using hc
  exact hc'.trans (Nat.choose_le_pow _ _)

noncomputable def keyCenter (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius) (g : Grid K) : Space :=
  lambda • oldAnchor P J (keyAnchor P key hk J radius e)+gridPoint K g

/-- A radius-two grid hit for every triangle; this is an actual measurable local set. -/
def keyBad (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius) :
    Set (keySupport P key hk J radius e → Space) :=
  ⋃ g : Grid K, ⋂ a : e.val,
    (fun p i => p (keyVertex P key hk J radius e a i)) ⁻¹'
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
        (keyCenter P key hk J radius lambda K e g) 2

theorem measurableSet_keyBad (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius) :
    MeasurableSet (keyBad P key hk J radius lambda K e) := by
  apply MeasurableSet.iUnion
  intro g
  apply MeasurableSet.iInter
  intro a
  exact (measurableSet_triangleHit _ _ _).preimage (by fun_prop)

/-- The actual global event is exactly the pullback of its local support predicate. -/
theorem mem_keyEvent (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius) (p : Vertex P → Space) :
    p ∈ localEvent (keySupport P key hk J radius) (keyBad P key hk J radius lambda K) e ↔
      ∃ g : Grid K, ∀ a : e.val,
        (fun i => p (triangleVertex P a.val i)) ∈
          triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
            (keyCenter P key hk J radius lambda K e g) 2 := by
  simp only [localEvent,keyBad,Set.mem_preimage,Set.mem_iUnion,Set.mem_iInter] <;> rfl

/-- Nonneighbor independence is derived from this event's actual variable supports. -/
theorem keyEvents_have_dependency_graph (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (ν : Vertex P → Measure Space)
    [∀ v, IsProbabilityMeasure (ν v)] :
    HasDependencyGraph (Measure.pi ν)
      (localEvent (keySupport P key hk J radius) (keyBad P key hk J radius lambda K))
      (supportGraph (keySupport P key hk J radius)) := by
  classical
  exact product_hasDependencyGraph ν (keySupport P key hk J radius)
    (keyBad P key hk J radius lambda K) (measurableSet_keyBad P key hk J radius lambda K)


/-- The chosen anchor minimizes the actual key on every original label in the event. -/
theorem keyAnchor_key_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) (a : Triangle P) (ha : a ∈ e.val) :
    key (keyAnchor P key hk J radius e) ≤ key a := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' key hk
  exact Finset.min'_le _ a ha

theorem keyAnchor_unique (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) (a : Triangle P) (ha : a ∈ e.val)
    (hmin : ∀ b ∈ e.val, key a ≤ key b) : keyAnchor P key hk J radius e = a := by
  apply hk
  exact Nat.le_antisymm (keyAnchor_key_le P key hk J radius e a ha)
    (hmin _ (keyAnchor_mem P key hk J radius e))

/-- Injectivity witnesses are proofs, not an additional anchor policy. -/
theorem keyAnchor_proof_irrel (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk hk' : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) :
    keyAnchor P key hk J radius e = keyAnchor P key hk' J radius e := rfl

end QEC.Coding.BDL26KeyedGeometric
