import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Events
import Mathlib.Data.List.Lex

/-! # Explicit four-label representation of each geometric event

Event order compares sorted lists of four input triangle ranks. It does not
extract an arbitrary enumeration of the event subtype.
-/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

noncomputable def eventScanKey (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : List ℕ :=
  (e.val.image (triangleKey P)).sort (· ≤ ·)

theorem eventScanKey_injective (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) : Function.Injective (eventScanKey P J radius) := by
  intro a b h
  have he := congrArg List.toFinset h
  simp only [eventScanKey,Finset.sort_toFinset] at he
  apply Subtype.ext
  exact Finset.image_injective (triangleKey_injective P) he

theorem eventScanKey_length (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : (eventScanKey P J radius e).length = 4 := by
  rw [eventScanKey,Finset.length_sort,Finset.card_image_of_injective _ (triangleKey_injective P)]
  exact e.property.1

end QEC.Coding.BDL26RandomPerturbation
