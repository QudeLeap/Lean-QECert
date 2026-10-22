import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.Rows

/-! # Physical Gibbs sectors of the actual recursive CSS Hamiltonian -/
noncomputable section
namespace QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)

/-- Every labelled check contributes, including repeated and identity rows. -/
def hamiltonian : Operator (Qubit.QubitRegister (Physical S n)) :=
  -∑ j : Sum (ZLabel S n) (XLabel S n), toQubitOperator (check S n j)

theorem hamiltonian_eq : hamiltonian S n = CSSGibbs.hamiltonian (zSyndrome S n) (xSyndrome S n) := rfl

abbrev projector := CSSGibbs.projector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
abbrev sector := CSSGibbs.sector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
abbrev realizable := CSSGibbs.Realizable (zSyndrome S n) (xSyndrome S n)
abbrev multiplicity := CSSGibbs.multiplicity (zSyndrome S n) (xSyndrome S n)
abbrev gibbs := CSSGibbs.gibbs (zSyndrome S n) (xSyndrome S n)
abbrev physicalPartition := CSSGibbs.physicalPartition (zSyndrome S n) (xSyndrome S n)
abbrev thermalExponential := CSSGibbs.thermalExponential (zSyndrome S n) (xSyndrome S n)

local instance : Fintype (LinearMap.range (zSyndrome S n)) := Fintype.ofFinite _
local instance : Fintype (LinearMap.range (xSyndrome S n)) := Fintype.ofFinite _

theorem zero_sector_code : sector S n 0 = (complex S n).binaryCSSCode.stabilizer.code.carrier := by
  exact (CSSGibbs.sector_zero_eq_code (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)).trans
    (code_carrier S n)

theorem zero_projector_code (v : Qubit.QubitRegister (Physical S n)) :
    projector S n 0 v = v ↔ v ∈ (complex S n).binaryCSSCode.stabilizer.code.carrier := by
  rw [← zero_sector_code]
  constructor
  · intro h; exact ⟨v, h⟩
  · rintro ⟨w, rfl⟩
    exact congrArg (fun A : Operator (Qubit.QubitRegister (Physical S n)) => A w)
      (CSSGibbs.projector_square _ _ (row_orthogonal S n) 0)

theorem projector_realizable (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n))) :
    projector S n s ≠ 0 ↔
      (fun z => s (.inl z)) ∈ LinearMap.range (zSyndrome S n) ∧
      (fun x => s (.inr x)) ∈ LinearMap.range (xSyndrome S n) := by
  rw [CSSGibbs.projector_ne_zero_iff, CSSGibbs.mem_realizableSyndromes_iff]

theorem sector_multiplicity (u : LinearMap.range (zSyndrome S n))
    (v : LinearMap.range (xSyndrome S n)) :
    Module.finrank ℂ (sector S n (CSSGibbs.joinSyndrome u.val v.val)) = multiplicity S n :=
  CSSGibbs.sector_realizable_finrank _ _ (row_orthogonal S n) u v

theorem multiplicity_positive : 0 < multiplicity S n := CSSGibbs.multiplicity_pos _ _

theorem multiplicity_cardinality : multiplicity S n * Fintype.card (realizable S n) =
    2 ^ Fintype.card (Physical S n) :=
  CSSGibbs.multiplicity_mul_card_realizable _ _ (row_orthogonal S n)

theorem hamiltonian_sector_energy (u : Word (ZMod 2) (ZLabel S n))
    (v : Word (ZMod 2) (XLabel S n)) :
    hamiltonian S n * projector S n (CSSGibbs.joinSyndrome u v) =
      ((-((Fintype.card (ZLabel S n) + Fintype.card (XLabel S n) : Nat) : ℝ) +
        2 * ((HammingWeight u : ℝ) + HammingWeight v) : ℝ) : ℂ) •
        projector S n (CSSGibbs.joinSyndrome u v) := by
  simpa only [hamiltonian_eq, CSSGibbs.energy_joinSyndrome, Nat.cast_add] using
    CSSGibbs.hamiltonian_mul_projector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
      (CSSGibbs.joinSyndrome u v)

theorem gibbs_normalized_exp (β : ℝ) : (gibbs S n β).toOperator =
    (physicalPartition S n β : ℂ)⁻¹ • thermalExponential S n β :=
  CSSGibbs.gibbs_normalized_exp _ _ β

theorem partition_formula (β : ℝ) : physicalPartition S n β =
    multiplicity S n * Real.exp (β * (Fintype.card (ZLabel S n) + Fintype.card (XLabel S n) : Nat)) *
      CSSGibbs.rowPartition (zSyndrome S n) (2 * β) * CSSGibbs.rowPartition (xSyndrome S n) (2 * β) :=
  CSSGibbs.physicalPartition_formula _ _ (row_orthogonal S n) β

/-- X errors have Z-row syndromes, on the actual degree-two coboundary image. -/
theorem xError_syndrome (e : Word (ZMod 2) (Physical S n)) : zSyndrome S n e =
    BDL26RZMap1CoordinateBridge.tannerCoboundary1 (presentation S n) e := rfl

/-- Z errors have X-row syndromes, on the literal transposed presentation. -/
theorem zError_syndrome (e : Word (ZMod 2) (Physical S n)) : xSyndrome S n e =
    BDL26RZMap1CoordinateBridge.tannerCoboundary1
      (BDL26FiniteTannerSquare.transposePresentation (presentation S n)) e := by
  exact DFunLike.congr_fun (xSyndrome_transposed S n) e

theorem gibbs_xError_marginal (β : ℝ) (u : LinearMap.range (zSyndrome S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * CSSGibbs.pMarginalProjector (zSyndrome S n) (xSyndrome S n)
        (row_orthogonal S n) u) = (CSSGibbs.rowProbability (zSyndrome S n) (2 * β) u : ℂ) :=
  CSSGibbs.gibbs_pMarginal_trace _ _ (row_orthogonal S n) β u

theorem gibbs_zError_marginal (β : ℝ) (v : LinearMap.range (xSyndrome S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * CSSGibbs.qMarginalProjector (zSyndrome S n) (xSyndrome S n)
        (row_orthogonal S n) v) = (CSSGibbs.rowProbability (xSyndrome S n) (2 * β) v : ℂ) :=
  CSSGibbs.gibbs_qMarginal_trace _ _ (row_orthogonal S n) β v

end QEC.Coding.BDL26CSSHamiltonian
