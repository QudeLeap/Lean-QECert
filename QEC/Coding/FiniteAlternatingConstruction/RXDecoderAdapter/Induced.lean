import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Regions

/-! # Actual RX induced identities -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

/-- Aggregate the actual X-to-Q maps on local cohomology classes. -/
noncomputable def actualGXQ0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    Word BDL26Field P.X →ₗ[BDL26Field] Word BDL26Field P.Q where
  toFun w q := ∑ x : P.X, if h : P.xq x q = true then
    rxCqH1Coordinate P q S (rxXQH0ToH1 P A q x h S (rxAggregateXH0 P x S w)) else 0
  map_add' a b := by
    funext q
    simp only [map_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp [apply_dite, apply_ite]
  map_smul' c w := by
    funext q
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp [apply_dite, apply_ite]

theorem actualGXQ0_eq_adjacency (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    actualGXQ0 P A S = rxXQAdjacency P := by
  apply LinearMap.ext
  intro w
  funext q
  exact (rxXQAdjacency_eq_sum_coordinates P A S w q).symm

/-- Aggregate both coordinates of the actual Q-to-Z cohomology maps. -/
noncomputable def actualGQZ1 (P : TannerSquarePresentation)
    (S : OddScale) : Word BDL26Field P.Q →ₗ[BDL26Field] Word BDL26Field (P.Z × Fin 2) where
  toFun w p := ∑ q : P.Q, if h : P.qz q p.1 = true then
    let pair := rxCzH2Coordinates P p.1
      (rxQZH1ToH2 P q p.1 h S (rxAggregateQH1 P q S w))
    if p.2 = 0 then pair.1 else pair.2
    else 0
  map_add' a b := by
    funext p
    simp only [map_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hp : p.2 = 0 <;> split <;> simp [hp]
  map_smul' c w := by
    funext p
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hp : p.2 = 0 <;> split <;> simp [hp]

theorem actualGQZ1_eq_diagonal (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    actualGQZ1 P S = RXCoarseGraining.diagonalMap.comp (rxQZAdjacency P) := by
  apply LinearMap.ext
  intro w
  funext p
  have h := rxQZDiagonal_eq_sum_coordinates P A S w p.1
  by_cases hb : p.2 = 0
  · have h0 := congrArg Prod.fst h
    simpa [actualGQZ1, hb, RXCoarseGraining.diagonalMap, Prod.fst_sum, apply_dite] using h0.symm
  · have h1 := congrArg Prod.snd h
    simpa [actualGQZ1, hb, RXCoarseGraining.diagonalMap, Prod.snd_sum, apply_dite] using h1.symm

end QEC.Coding.BDL26RXDecoderAdapter
