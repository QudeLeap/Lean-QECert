import QEC.Coding.ExpanderCodes.LPSGoodFamilyAssembly
import QEC.Coding.ExpanderCodes.LPSSparseEmitterFamilyMachine

/-!
# Explicit PK22 code families conditional on the LPS spectral theorem

For any fixed finite field and target rate, the coding construction and the
actual sparse-check machine are proved together. The sole external premise is
the complex zero-sum operator bound on the selected, unnormalized LPS graphs.
It does not assume local-code expansion, code goodness, or an output algorithm.

Source: [PK22, Main qLDPC Theorem and Example 9]. This is the explicitly
conditional project composition of that source, not an unconditional proof
of the external LPS theorem.
-/

namespace QEC.Coding.TannerLiftedProduct

open scoped MatrixGroups
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing

noncomputable local instance {F : Type} : DecidableEq F := Classical.decEq _

noncomputable local instance pk22ConditionalQubitDecidableEq
    {p : ℕ} {R R' : Type} (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    DecidableEq
      (FamilyQubitIndex (W := Fin (p + 1)) (R := R) (R' := R')
        (G := LPSVertexGroup hp hp4) B) :=
  Classical.decEq _

/-- An explicit good PK22 family and its polynomial-in-physical-length sparse
output program, under the external LPS bound on the actual selected graphs.
The same field tables, local matrices, program and polynomial serve the whole
cofinal family. Decoded output cuts out the carrier of that very family. -/
theorem exists_explicit_good_family_of_lps_spectral_bound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate) (hRate : targetRate < 1)
    (hLPS : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ),
      SmallSetExpansion.HasMeanZeroComplexOperatorBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 B))
        (2 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F)
      (e : Fin (Fintype.card F) ≃ F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one a.prime a.oneModFour
      let family := lpsSemanticFamily a.prime a.oneModFour hCount h h'
      let r := pk22RowCoefficient (Nat.card F) t * a.blocks
      let tables := encodedFieldTables e
      let g := LPSSparseEmitterFamily.sourceDirections a.prime a.oneModFour
      let hc := h.map e.symm
      let hc' := h'.map e.symm
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily family ∧
      QEC.QLDPC.HasEventualRateAtLeast family targetRate ∧
      (∀ B : ℕ,
        LPSSparseEmitterFamily.physicalSize
          (lpsEffectiveResiduePrimeAt a.prime a.oneModFour B) (a.p + 1) r r =
            family.blockLength B) ∧
      (∀ B : ℕ, Nonempty (TM2OutputsInTime
        (LPSSparseEmitterFamily.sourceMachine a.prime a.oneModFour tables hc hc').toFinTM2
        (unary B)
        (some (LPSSparseEmitterFamily.sourceOutput a.prime a.oneModFour B tables hc hc'))
        ((LPSSparseEmitterFamily.sourceTime a.prime a.oneModFour tables hc hc').eval
          (family.blockLength B)))) ∧
      (∀ B : ℕ,
        LPSSparseEmitterCodec.decodeTyped
          (LPSSparseEmitterFamily.PhysicalCount
            (lpsEffectiveResiduePrimeAt a.prime a.oneModFour B).q (a.p + 1) r r)
          (Fintype.card F)
          (LPSSparseEmitterFamily.sourceOutput a.prime a.oneModFour B tables hc hc') =
        some (lpsEncodedCheckOutput tables
          (fun j => lpsEffectiveQuaternionFamilyIndex a.prime a.oneModFour B (g j))
          hc hc')) ∧
      (∀ (B : ℕ)
        (ψ : Semantics.Qudit.QuditRegister
          (fun _ : FamilyQubitIndex
            (W := Fin (a.p + 1)) (R := PK22Check (Nat.card F) t a)
            (R' := PK22Check (Nat.card F) t a)
            (G := LPSVertexGroup a.prime a.oneModFour) B => Fintype.card F)),
        ψ ∈ (family.presentation B).code.carrier ↔
          ∀ i : Fin (LPSSparseEmitterFamily.CheckCount
            (lpsEffectiveResiduePrimeAt a.prime a.oneModFour B).q
            (a.p + 1) r r (Fintype.card F)),
          LPSSparseEmitterFamily.decodedOperator e tables i
            (LPSSparseEmitterFamily.sourceOutput a.prime a.oneModFour B tables hc hc') ψ = ψ) := by
  classical
  obtain ⟨t, a, h, h', hGood, hRequestedRate⟩ :=
    exists_pk22LPSFamily_of_ramanujanComplexOperatorBound
      F targetRate hRatePositive hRate hLPS
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  refine ⟨t, a, h, h', e, hGood, hRequestedRate, ?_, ?_, ?_, ?_⟩
  · intro B
    rfl
  · intro B
    exact ⟨Machine.outputsInTime _ _ _ _
      (LPSSparseEmitterFamily.sourceExec a.prime a.oneModFour B
        (encodedFieldTables e) (h.map e.symm) (h'.map e.symm))⟩
  · intro B
    exact LPSSparseEmitterFamily.decodeTyped_output
      a.prime a.oneModFour B
      (LPSSparseEmitterFamily.sourceDirections a.prime a.oneModFour)
      (encodedFieldTables e) (h.map e.symm) (h'.map e.symm)
  · intro B ψ
    exact LPSSparseEmitterFamily.mem_originalFamily_carrier_iff_decodedOutput
      e a.prime a.oneModFour B
      (LPSSparseEmitterFamily.sourceDirections a.prime a.oneModFour) h h' ψ

end QEC.Coding.TannerLiftedProduct
