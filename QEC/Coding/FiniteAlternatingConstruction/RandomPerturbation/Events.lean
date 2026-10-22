import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Finite support-local geometric bad events

An event groups four monochromatic triangle labels whose old X anchors are close.
Its deterministic center grid is fixed before sampling. All net centers are
combined inside one event, so the dependency degree will not grow with the grid.
-/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

noncomputable def oldAnchor (P : TannerSquarePresentation) (J : Vertex P → Space)
    (a : Triangle P) : Space := (1/2 : ℝ) • J (.x (P.faceX a.1))

def Eligible (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ)
    (s : Finset (Triangle P)) : Prop :=
  s.card = 4 ∧
    (∀ a ∈ s, ∀ b ∈ s, triangleColor P a = triangleColor P b) ∧
    ∀ a ∈ s, ∀ b ∈ s, dist (oldAnchor P J a) (oldAnchor P J b) ≤ radius

abbrev Event (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ) :=
  {s : Finset (Triangle P) // Eligible P J radius s}

noncomputable instance eventFintype (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) : Fintype (Event P J radius) := Fintype.ofFinite _

theorem event_nonempty (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ)
    (e : Event P J radius) : e.val.Nonempty := by
  apply Finset.card_pos.mp
  rw [e.property.1]
  norm_num

/-- The least enumerated label gives a deterministic anchor, independent of samples. -/
noncomputable def eventAnchor (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : Triangle P := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' (triangleKey P) (triangleKey_injective P)
  exact e.val.min' (event_nonempty P J radius e)

theorem eventAnchor_mem (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ)
    (e : Event P J radius) : eventAnchor P J radius e ∈ e.val := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' (triangleKey P) (triangleKey_injective P)
  exact Finset.min'_mem e.val (event_nonempty P J radius e)

/-- Only the actual domain vertices are resampled. -/
noncomputable def eventSupport (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : Finset (Vertex P) := by
  classical
  exact e.val.biUnion (triangleSupport P)

theorem eventSupport_card_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : (eventSupport P J radius e).card ≤ 12 := by
  classical
  calc
    _ ≤ ∑ a ∈ e.val, (triangleSupport P a).card := Finset.card_biUnion_le
    _ = e.val.card*3 := by simp [triangleSupport_card]
    _ = 12 := by norm_num [e.property.1]

/-- Each local triangle coordinate refers to the corresponding variable in the union. -/
def eventVertex (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ)
    (e : Event P J radius) (a : e.val) (i : Fin 3) : eventSupport P J radius e :=
  ⟨triangleVertex P a.val i, by
    classical
    exact Finset.mem_biUnion.mpr ⟨a.val,a.property,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩⟩

theorem event_card_le (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ) :
    Fintype.card (Event P J radius) ≤ Fintype.card (Triangle P)^4 := by
  classical
  let encode : Event P J radius → ↥((Finset.univ : Finset (Triangle P)).powersetCard 4) :=
    fun e => ⟨e.val,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,e.property.1⟩⟩
  have hinj : Function.Injective encode := by
    intro e f h
    have he := congrArg (fun s : ↥((Finset.univ : Finset (Triangle P)).powersetCard 4) => s.val) h
    exact Subtype.ext he
  have hc := Fintype.card_le_of_injective encode hinj
  have hc' : Fintype.card (Event P J radius) ≤ (Fintype.card (Triangle P)).choose 4 := by
    simpa only [Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ] using hc
  exact hc'.trans (Nat.choose_le_pow _ _)

noncomputable def eventCenter (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) (g : Grid K) : Space :=
  lambda • oldAnchor P J (eventAnchor P J radius e)+gridPoint K g

/-- A radius-two grid hit for every triangle; this is an actual measurable local set. -/
def eventBad (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) :
    Set (eventSupport P J radius e → Space) :=
  ⋃ g : Grid K, ⋂ a : e.val,
    (fun p i => p (eventVertex P J radius e a i)) ⁻¹'
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
        (eventCenter P J radius lambda K e g) 2

theorem measurableSet_eventBad (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) :
    MeasurableSet (eventBad P J radius lambda K e) := by
  apply MeasurableSet.iUnion
  intro g
  apply MeasurableSet.iInter
  intro a
  exact (measurableSet_triangleHit _ _ _).preimage (by fun_prop)

/-- The actual global event is exactly the pullback of its local support predicate. -/
theorem mem_global_event (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) (p : Vertex P → Space) :
    p ∈ localEvent (eventSupport P J radius) (eventBad P J radius lambda K) e ↔
      ∃ g : Grid K, ∀ a : e.val,
        (fun i => p (triangleVertex P a.val i)) ∈
          triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
            (eventCenter P J radius lambda K e g) 2 := by
  simp only [localEvent,eventBad,Set.mem_preimage,Set.mem_iUnion,Set.mem_iInter] <;> rfl

/-- Nonneighbor independence is derived from this event's actual variable supports. -/
theorem events_have_dependency_graph (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (ν : Vertex P → Measure Space)
    [∀ v, IsProbabilityMeasure (ν v)] :
    HasDependencyGraph (Measure.pi ν)
      (localEvent (eventSupport P J radius) (eventBad P J radius lambda K))
      (supportGraph (eventSupport P J radius)) := by
  classical
  exact product_hasDependencyGraph ν (eventSupport P J radius)
    (eventBad P J radius lambda K) (measurableSet_eventBad P J radius lambda K)

end QEC.Coding.BDL26RandomPerturbation
