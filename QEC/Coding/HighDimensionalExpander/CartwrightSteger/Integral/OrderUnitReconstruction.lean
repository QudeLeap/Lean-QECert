import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewFaithfulness
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewReconstructionTheorem

/-!
# Reconstructing integral order units in the skew presentation

If an order unit and its inverse are integral at the building place, the
coordinate reconstruction produces mutually inverse skew Laurent elements.
Faithfulness of the global representation supplies both inverse identities.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- An order unit whose two unit components are building-integral has a
genuine preimage in the unit group of the integral skew Laurent ring. -/
theorem exists_skewLaurentUnit_of_orderUnit_and_buildingIntegral
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (u : CartwrightStegerOrder P r)))
    (hlocalInv : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
              CartwrightStegerOrder P r))) :
    ∃ v : (CartwrightStegerSkewLaurentRing P r)ˣ,
      skewLaurentToGlobalMatrix P r v =
        (cartwrightStegerOrderToCyclicAlgebra P r
          (u : CartwrightStegerOrder P r)).1 := by
  obtain ⟨f, hf⟩ := exists_skewLaurent_of_order_and_buildingIntegral
    P r (u : CartwrightStegerOrder P r) hlocal
  obtain ⟨g, hg⟩ := exists_skewLaurent_of_order_and_buildingIntegral
    P r ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
      CartwrightStegerOrder P r) hlocalInv
  have hfg : f * g = 1 := by
    apply skewLaurentToGlobalMatrix_injective P r
    rw [map_mul, hf, hg, map_one]
    have hu : (u : CartwrightStegerOrder P r) *
        ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
          CartwrightStegerOrder P r) = 1 := u.val_inv
    exact congrArg Subtype.val
      (congrArg (cartwrightStegerOrderToCyclicAlgebra P r) hu)
  have hgf : g * f = 1 := by
    apply skewLaurentToGlobalMatrix_injective P r
    rw [map_mul, hf, hg, map_one]
    have hu : ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
        CartwrightStegerOrder P r) *
        (u : CartwrightStegerOrder P r) = 1 := u.inv_val
    exact congrArg Subtype.val
      (congrArg (cartwrightStegerOrderToCyclicAlgebra P r) hu)
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
