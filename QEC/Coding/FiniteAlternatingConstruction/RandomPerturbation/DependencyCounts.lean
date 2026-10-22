import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.LocalCounts

/-! # Scale-independent degree of the actual geometric dependency graph -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

noncomputable def eventsAtTriangle (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (a : Triangle P) : Finset (Event P J K) := by
  classical
  exact Finset.univ.filter (fun e => a ∈ e.val)

noncomputable def eventsAtVertex (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (v : Vertex P) : Finset (Event P J K) := by
  classical
  exact Finset.univ.filter (fun e => v ∈ eventSupport P J K e)

/-- Erasing the fixed label injects four-triangle events into local three-element subsets. -/
theorem eventsAtTriangle_card_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ) (a : Triangle P) (hpool : (localPool P J K a).card ≤ M) :
    (eventsAtTriangle P J K a).card ≤ M^3 := by
  classical
  have hc : (eventsAtTriangle P J K a).card ≤ ((localPool P J K a).powersetCard 3).card := by
    apply Finset.card_le_card_of_injOn (fun e : Event P J K => e.val.erase a)
    · intro e he
      have ha : a ∈ e.val := (Finset.mem_filter.mp he).2
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro b hb
        have heb : b ∈ e.val := Finset.mem_of_mem_erase hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.property.2.2 a ha b heb⟩
      · rw [Finset.card_erase_of_mem ha,e.property.1]
    · intro e he f hf hef
      have hea : a ∈ e.val := (Finset.mem_filter.mp he).2
      have hfa : a ∈ f.val := (Finset.mem_filter.mp hf).2
      apply Subtype.ext
      calc
        e.val = insert a (e.val.erase a) := (Finset.insert_erase hea).symm
        _ = insert a (f.val.erase a) := congrArg (insert a) hef
        _ = f.val := Finset.insert_erase hfa
  rw [Finset.card_powersetCard] at hc
  exact hc.trans ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hpool 3))

theorem eventsAtVertex_subset (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (v : Vertex P) :
    eventsAtVertex P J K v ⊆ (incidentTriangles P v).biUnion (eventsAtTriangle P J K) := by
  classical
  intro e he
  have hv : v ∈ eventSupport P J K e := (Finset.mem_filter.mp he).2
  obtain ⟨a,ha,hva⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨a,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hva⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩

/-- A touched vertex chooses at most 56 incident triangles, then at most M^3 events. -/
theorem eventsAtVertex_card_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ) (hv : BoundedValence P)
    (hpool : ∀ a, (localPool P J K a).card ≤ M) (v : Vertex P) :
    (eventsAtVertex P J K v).card ≤ 56*M^3 := by
  classical
  calc
    _ ≤ ((incidentTriangles P v).biUnion (eventsAtTriangle P J K)).card :=
      Finset.card_le_card (eventsAtVertex_subset P J K v)
    _ ≤ ∑ a ∈ incidentTriangles P v, (eventsAtTriangle P J K a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ incidentTriangles P v, M^3 :=
      Finset.sum_le_sum (fun a _ => eventsAtTriangle_card_le P J K M a (hpool a))
    _ = (incidentTriangles P v).card*M^3 := by simp
    _ ≤ 56*M^3 := Nat.mul_le_mul_right _ (incidentTriangles_card_le P hv v)

/-- Every actual graph neighbor touches one of the event's actual support vertices. -/
theorem neighbors_subset_touched (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (e : Event P J K) :
    (supportGraph (eventSupport P J K)).neighborFinset e ⊆
      (eventSupport P J K e).biUnion (eventsAtVertex P J K) := by
  classical
  intro f hf
  have hadj : (supportGraph (eventSupport P J K)).Adj e f := by
    simpa only [SimpleGraph.mem_neighborFinset] using hf
  obtain ⟨v,hve,hvf⟩ := Finset.not_disjoint_iff.mp hadj.2
  exact Finset.mem_biUnion.mpr ⟨v,hve,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvf⟩⟩

/-- The derived degree bound contains no perturbation scale or global input size. -/
theorem event_degree_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ)
    (hv : BoundedValence P) (hpool : ∀ a, (localPool P J K a).card ≤ M)
    (e : Event P J K) :
    ((supportGraph (eventSupport P J K)).neighborFinset e).card ≤ 12*56*M^3 := by
  classical
  calc
    _ ≤ ((eventSupport P J K e).biUnion (eventsAtVertex P J K)).card :=
      Finset.card_le_card (neighbors_subset_touched P J K e)
    _ ≤ ∑ v ∈ eventSupport P J K e, (eventsAtVertex P J K v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ eventSupport P J K e, 56*M^3 :=
      Finset.sum_le_sum (fun v _ => eventsAtVertex_card_le P J K M hv hpool v)
    _ = (eventSupport P J K e).card*(56*M^3) := by simp
    _ ≤ 12*(56*M^3) := Nat.mul_le_mul_right _ (eventSupport_card_le P J K e)
    _ = 12*56*M^3 := by ring

/-- Incoming density supplies every local-pool hypothesis used in the degree proof. -/
theorem event_degree_le_of_density (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ)
    (t : ℝ) (hJ : BDL26ReplacementEmbedding.IsBoundedDensityLocalMap P J t)
    (hv : BoundedValence P) (hM : (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ))
    (e : Event P J K) :
    ((supportGraph (eventSupport P J K)).neighborFinset e).card ≤ 12*56*M^3 :=
  event_degree_le P J K M hv (localPool_card_le_integer P J t hJ K M hM) e

end QEC.Coding.BDL26RandomPerturbation
