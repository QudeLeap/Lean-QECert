import QEC.Coding.QuditQubitConversion.AppendixANF.Gate.ListStructure

/-!
# Compositional gate-list ANF certificates for WHY24 Appendix A

The proofs below use generic finite-list algebra and the structural
certificates for the printed pair and triple lists.  They do not enumerate
Boolean input words or the ambient coordinate products.
-/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

open scoped BigOperators
open Why24BooleanANF

private theorem listSum_eq_fintypeIndicator
    {Entry Value : Type*} [Fintype Entry] [BEq Entry] [LawfulBEq Entry]
    [DecidableEq Entry]
    [AddCommMonoid Value] (entries : List Entry) (hentries : entries.Nodup)
    (value : Entry → Value) :
    (entries.map value).sum =
      ∑ entry : Entry, if entry ∈ entries then value entry else 0 := by
  classical
  calc
    (entries.map value).sum = ∑ entry ∈ entries.toFinset, value entry :=
      (List.sum_toFinset value hentries).symm
    _ = ∑ entry ∈ entries.toFinset,
        if entry ∈ entries then value entry else 0 := by
          apply Finset.sum_congr rfl
          intro entry hentry
          simp only [List.mem_toFinset.mp hentry, if_pos]
    _ = ∑ entry ∈ (Finset.univ : Finset Entry),
        if entry ∈ entries then value entry else 0 := by
          apply Finset.sum_subset (Finset.subset_univ entries.toFinset)
          intro entry _ hentry
          have hnot : entry ∉ entries := fun hmem =>
            hentry (List.mem_toFinset.mpr hmem)
          rw [if_neg hnot]
    _ = ∑ entry : Entry, if entry ∈ entries then value entry else 0 := rfl

private theorem listSum_eq_orderedCoefficient
    {Entry Value : Type*} [Fintype Entry] [BEq Entry] [LawfulBEq Entry]
    [DecidableEq Entry]
    [AddCommMonoid Value] [Module (ZMod 2) Value]
    (entries : List Entry) (hentries : entries.Nodup)
    (ordered : Entry → Prop) [DecidablePred ordered]
    (hordered : ∀ entry ∈ entries, ordered entry)
    (coefficient : Entry → ZMod 2)
    (hcoefficient : ∀ entry, coefficient entry =
      if entry ∈ entries then 1 else 0)
    (value : Entry → Value) :
    (entries.map value).sum =
      ∑ entry : Entry, if ordered entry then
        coefficient entry • value entry
      else 0 := by
  rw [listSum_eq_fintypeIndicator entries hentries]
  apply Finset.sum_congr rfl
  intro entry _
  by_cases hmem : entry ∈ entries
  · have hord := hordered entry hmem
    simp [hmem, hord, hcoefficient entry]
  · simp [hmem, hcoefficient entry]

/-- The printed quadratic list sums to its normalized sparse ANF slice. -/
theorem quadraticGatePairs_ANF_sum :
    (quadraticGatePairs.map
      (fun pair => generator pair.1 * generator pair.2)).sum =
      ∑ pair : Fin 10 × Fin 10, if pair.1 < pair.2 then
        quadraticGateCoefficient pair.1 pair.2 •
          (generator pair.1 * generator pair.2)
      else 0 := by
  exact listSum_eq_orderedCoefficient quadraticGatePairs
    quadraticGatePairs_nodup (fun pair => pair.1 < pair.2)
    quadraticGatePairs_ordered
    (fun pair => quadraticGateCoefficient pair.1 pair.2)
    quadraticGateCoefficient_eq_indicator
    (fun pair => generator pair.1 * generator pair.2)

/-- The printed cubic list sums to its normalized sparse ANF slice. -/
theorem cubicGateTriples_ANF_sum :
    (cubicGateTriples.map
      (fun triple => generator triple.1 * generator triple.2.1 *
        generator triple.2.2)).sum =
      ∑ triple : Fin 10 × Fin 10 × Fin 10,
        if triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2 then
          cubicGateCoefficient triple.1 triple.2.1 triple.2.2 •
            (generator triple.1 * generator triple.2.1 *
              generator triple.2.2)
        else 0 := by
  exact listSum_eq_orderedCoefficient cubicGateTriples
    cubicGateTriples_nodup
    (fun triple => triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2)
    cubicGateTriples_ordered
    (fun triple => cubicGateCoefficient triple.1 triple.2.1 triple.2.2)
    cubicGateCoefficient_eq_indicator
    (fun triple => generator triple.1 * generator triple.2.1 *
      generator triple.2.2)

end QEC.Coding.Why24AppendixANF
