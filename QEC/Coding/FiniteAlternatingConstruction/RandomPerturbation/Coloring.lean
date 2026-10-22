import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Incidence

/-!
# Finite incidence-rank coloring

A triple of local ranks gives a proper coloring of labeled triangles with
56^3 colors. This conservative constant avoids any dependence on input density.
The ranks are counts in explicitly enumerated finite fibers.
-/

namespace QEC.Coding.BDL26RandomPerturbation

open BDL26FiniteTannerSquare BDL26BoundedValence

section FiberRank
variable {T A : Type*} [Fintype T] [DecidableEq T] [DecidableEq A]
variable (key : T → ℕ) (f : T → A)

/-- Earlier labels in the same incidence fiber. -/
def earlierFiber (a : T) : Finset T :=
  Finset.univ.filter fun b => f b = f a ∧ key b < key a

def fiberRank (a : T) : ℕ := (earlierFiber key f a).card

theorem fiberRank_lt_card (a : T) :
    fiberRank key f a < (Finset.univ.filter fun b => f b = f a).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro b hb
    simp only [earlierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb.1
  · intro he
    have ha : a ∈ Finset.univ.filter (fun b => f b = f a) := by simp
    rw [← he] at ha
    simpa [earlierFiber] using ha

theorem fiberRank_strictMono (a b : T) (hf : f a = f b) (hk : key a < key b) :
    fiberRank key f a < fiberRank key f b := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro t ht
    simp only [earlierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨ht.1.trans hf, ht.2.trans hk⟩
  · intro he
    have ha : a ∈ earlierFiber key f b := by simp [earlierFiber, hf, hk]
    rw [← he] at ha
    simpa [earlierFiber] using ha

theorem fiberRank_injective_on_fiber (hkey : Function.Injective key)
    (a b : T) (hf : f a = f b) (hr : fiberRank key f a = fiberRank key f b) : a = b := by
  rcases lt_trichotomy (key a) (key b) with hab | hab | hab
  · have h := fiberRank_strictMono key f a b hf hab
    omega
  · exact hkey hab
  · have h := fiberRank_strictMono key f b a hf.symm hab
    omega

end FiberRank

noncomputable section TriangleColor
variable (P : TannerSquarePresentation)

/-- A fixed enumeration of domain labels, not an ordering of image points. -/
def triangleKey (t : Triangle P) : ℕ := (Fintype.equivFin (Triangle P) t).val

theorem triangleKey_injective : Function.Injective (triangleKey P) := by
  intro a b h
  apply (Fintype.equivFin (Triangle P)).injective
  exact Fin.ext h

/-- Local ranks at the three types of vertices. -/
def triangleColor (t : Triangle P) : Fin 3 → ℕ := by
  classical
  exact ![fiberRank (triangleKey P) (fun t : Triangle P => P.faceX t.1) t,
    fiberRank (triangleKey P) (fun t : Triangle P => P.faceQ t.1 t.2) t,
    fiberRank (triangleKey P) (fun t : Triangle P => P.faceZ t.1) t]

theorem triangleColor_lt (hv : BoundedValence P) (t : Triangle P) (i : Fin 3) :
    triangleColor P t i < 56 := by
  classical
  fin_cases i
  · have hr := fiberRank_lt_card (triangleKey P) (fun t : Triangle P => P.faceX t.1) t
    have hc := xTriangles_card_le P hv (P.faceX t.1)
    simp only [XTriangles, Fintype.card_subtype] at hc
    change fiberRank (triangleKey P) (fun t : Triangle P => P.faceX t.1) t < 56
    omega
  · have hr := fiberRank_lt_card (triangleKey P) (fun t : Triangle P => P.faceQ t.1 t.2) t
    have hc := qTriangles_card_le P hv (P.faceQ t.1 t.2)
    simp only [QTriangles, Fintype.card_subtype] at hc
    change fiberRank (triangleKey P) (fun t : Triangle P => P.faceQ t.1 t.2) t < 56
    omega
  · have hr := fiberRank_lt_card (triangleKey P) (fun t : Triangle P => P.faceZ t.1) t
    have hc := zTriangles_card_le P hv (P.faceZ t.1)
    simp only [ZTriangles, Fintype.card_subtype] at hc
    change fiberRank (triangleKey P) (fun t : Triangle P => P.faceZ t.1) t < 56
    omega

/-- Equal colors and a common domain vertex force the same triangle label. -/
theorem triangleColor_same_vertex {a b : Triangle P}
    (hc : triangleColor P a = triangleColor P b) {i j : Fin 3}
    (hv : triangleVertex P a i = triangleVertex P b j) : a = b := by
  classical
  fin_cases i <;> fin_cases j <;> simp [triangleVertex] at hv
  · apply fiberRank_injective_on_fiber (triangleKey P) (fun t : Triangle P => P.faceX t.1)
      (triangleKey_injective P) a b
    · exact hv
    · exact congrFun hc 0
  · apply fiberRank_injective_on_fiber (triangleKey P) (fun t : Triangle P => P.faceQ t.1 t.2)
      (triangleKey_injective P) a b
    · exact hv
    · exact congrFun hc 1
  · apply fiberRank_injective_on_fiber (triangleKey P) (fun t : Triangle P => P.faceZ t.1)
      (triangleKey_injective P) a b
    · exact hv
    · exact congrFun hc 2

/-- Disjoint supports in a color class justify independent triangle-hit events. -/
theorem triangleSupport_disjoint_of_color {a b : Triangle P} (hne : a ≠ b)
    (hc : triangleColor P a = triangleColor P b) :
    Disjoint (triangleSupport P a) (triangleSupport P b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v ha hb
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
  exact hne (triangleColor_same_vertex P hc (hi.trans hj.symm))

/-- A fixed finite color codomain for density counting. -/
def boundedTriangleColor (hv : BoundedValence P) (t : Triangle P) : Fin 3 → Fin 56 :=
  fun i => ⟨triangleColor P t i, triangleColor_lt P hv t i⟩

theorem boundedTriangleColor_card : Fintype.card (Fin 3 → Fin 56) = 56 ^ 3 := by simp

end TriangleColor
end QEC.Coding.BDL26RandomPerturbation
