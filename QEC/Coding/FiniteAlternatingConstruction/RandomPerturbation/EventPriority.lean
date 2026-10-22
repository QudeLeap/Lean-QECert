import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventEncoding

/-! # Explicit lex-key priority for the concrete event universe

The event subtype also inherits finite-set inclusion. Named priority prevents
that unrelated relation from being inferred for sorted execution metadata.
-/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

def eventPriorityLE (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) : Prop := eventScanKey P J r e ≤ eventScanKey P J r f

noncomputable instance eventPriorityDecidable (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) : DecidableRel (eventPriorityLE P J r) := fun e f =>
  inferInstanceAs (Decidable (eventScanKey P J r e ≤ eventScanKey P J r f))

instance eventPriorityTrans (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ) :
    IsTrans (Event P J r) (eventPriorityLE P J r) :=
  ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩

instance eventPriorityAntisymm (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ) :
    Std.Antisymm (eventPriorityLE P J r) :=
  ⟨fun _ _ h1 h2 => eventScanKey_injective P J r (le_antisymm h1 h2)⟩

instance eventPriorityTotal (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ) :
    Std.Total (eventPriorityLE P J r) := ⟨fun _ _ => le_total _ _⟩

end QEC.Coding.BDL26RandomPerturbation
