import QEC.Coding.Stabilizer.GoodSyndromeProtectedSector
import QEC.Semantics.Dynamics.ProtectedObservableDecay
/-!
# Stable-syndrome quantitative storage bridge

This module closes the M11 composition route.  The first theorem converts the
exact CLBT10 all-time displacement estimate into an operational storage
horizon, retaining the target tolerance, factor eight, dissipator norm, and
Gibbs tail mass.  The second theorem derives the protected logical pair and
good-sector hypotheses from the stabilizer decoder adapter.

The zero-rate case is stated without division: when the dissipator norm times
the bad-sector Gibbs mass vanishes, both encoded and decoded displacement are
zero for every nonnegative time.  No Gibbs-tail estimate or energy-barrier
implication is introduced here.
-/

noncomputable section

namespace QEC.Semantics

open QEC.Coding.StabilizerCode
open QEC.Coding.PauliSymplectic

variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]

/-! ## Quantitative corollary of the exact CLBT theorem -/

/--
The exact CLBT displacement estimate gives an encoded and decoded storage
horizon at every nonnegative target tolerance.  The final conjunct records the
zero-rate branch explicitly, so no division by a vanishing rate is used.
-/
theorem protectedObservableStorageHorizon
    {a : Type} [Nontrivial K] [Fintype a]
    (logical : ThermalEncoding.PauliLikePair K)
    (hamiltonian : Operator K) (hhamiltonian : hamiltonian.IsSymmetric)
    (beta : ℝ) (J : a → Operator K) (P : Operator K)
    (hP : IsStarProjection P)
    (hPx : Commute P logical.x) (hPz : Commute P logical.z)
    (hHx : Commute hamiltonian logical.x)
    (hHz : Commute hamiltonian logical.z)
    (hPH : Commute P hamiltonian)
    (hprotectedX : JumpProtected J logical.x P)
    (hprotectedZ : JumpProtected J logical.z P)
    (hstationary : lindbladDissipator J
      (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta).toOperator = 0) :
    ∃ Enc : QuantumChannel Qubit.QubitSpace K,
      ∃ Dec : QuantumChannel K Qubit.QubitSpace,
        (∀ eta : DensityOperator Qubit.QubitSpace,
          Dec.mapDensity (Enc.mapDensity eta) = eta) ∧
        (∀ (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ)
            (_hdelta : 0 ≤ delta) (ht : 0 ≤ t),
          8 * t * lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) ≤
            delta →
          traceNorm
              (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t
                    ht)
                  |>.mapDensity (Enc.mapDensity eta)).toOperator -
                (Enc.mapDensity eta).toOperator) ≤ delta ∧
          traceNorm
              ((Dec.mapDensity
                  ((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t
                      ht)
                    |>.mapDensity (Enc.mapDensity eta))).toOperator -
                eta.toOperator) ≤ delta) ∧
        (lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) = 0 →
          ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
            traceNorm
                (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                    |>.mapDensity (Enc.mapDensity eta)).toOperator -
                  (Enc.mapDensity eta).toOperator) = 0 ∧
            traceNorm
                ((Dec.mapDensity
                    ((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                      |>.mapDensity (Enc.mapDensity eta))).toOperator -
                  eta.toOperator) = 0) := by
  rcases clbtProtectedObservableDecay logical hamiltonian hhamiltonian beta J P
      hP hPx hPz hHx hHz hPH hprotectedX hprotectedZ hstationary with
    ⟨Enc, Dec, hleftInverse, hdecay⟩
  have hhorizon :
      ∀ (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ)
          (_hdelta : 0 ≤ delta) (ht : 0 ≤ t),
        8 * t * lindbladDissipatorNorm J *
            clbtGibbsTailMass P
              (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) ≤
          delta →
        traceNorm
            (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                |>.mapDensity (Enc.mapDensity eta)).toOperator -
              (Enc.mapDensity eta).toOperator) ≤ delta ∧
        traceNorm
            ((Dec.mapDensity
                ((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                  |>.mapDensity (Enc.mapDensity eta))).toOperator -
              eta.toOperator) ≤ delta := by
    intro eta delta t _hdelta ht hwindow
    let evolved :=
      (finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht).mapDensity
        (Enc.mapDensity eta)
    have hencoded :
        traceNorm (evolved.toOperator - (Enc.mapDensity eta).toOperator) ≤
          delta :=
      (hdecay eta t ht).trans hwindow
    have hdecoded :
        traceNorm
            ((Dec.mapDensity evolved).toOperator - eta.toOperator) ≤ delta := by
      have hcontract :=
        Dec.traceNorm_density_sub_le evolved (Enc.mapDensity eta)
      have hleftOperator :
          Dec (Enc.mapDensity eta).toOperator = eta.toOperator := by
        rw [← QuantumChannel.mapDensity_toOperator]
        exact congrArg DensityOperator.toOperator (hleftInverse eta)
      rw [hleftOperator] at hcontract
      simpa only [QuantumChannel.mapDensity_toOperator] using
        hcontract.trans hencoded
    exact ⟨hencoded, hdecoded⟩
  refine ⟨Enc, Dec, hleftInverse, hhorizon, ?_⟩
  intro hzero eta t ht
  have hwindow :
      8 * t * lindbladDissipatorNorm J *
          clbtGibbsTailMass P
            (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) ≤
        0 := by
    calc
      8 * t * lindbladDissipatorNorm J *
            clbtGibbsTailMass P
              (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) =
          8 * t *
            (lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta)) := by
              ring
      _ = 0 := by rw [hzero, mul_zero]
      _ ≤ 0 := le_refl 0
  rcases hhorizon eta 0 t (le_refl 0) ht hwindow with
    ⟨hencoded, hdecoded⟩
  exact ⟨le_antisymm hencoded (traceNorm_nonneg _),
    le_antisymm hdecoded (traceNorm_nonneg _)⟩

/-! ## Stabilizer good-syndrome specialization -/

/--
The public M11 bridge.  The Pauli-like pair, protected good sector, jump
protectedness, and Gibbs bad-sector identity are all derived from the concrete
decoder and selected elementary Pauli errors.  The only dynamical premise is
the source-required stationarity of the resulting Gibbs state.
-/
theorem stableSyndromeLifetimeBridge
    {iota kappa a : Type}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa] [Fintype a]
    (H : LocalStabilizerHamiltonian (ι := iota) (κ := kappa))
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary iota))
    (jumpError : a → Binary iota)
    (hjumpError : ∀ b, jumpError b ∈ elementaryErrors)
    (beta : ℝ) :
    let logical : ThermalEncoding.PauliLikePair (Qubit.QubitRegister iota) :=
      { x := D.dressedX
        z := D.dressedZ
        x_symmetric :=
          (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedX).mpr
            D.dressedX_adjoint
        z_symmetric :=
          (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedZ).mpr
            D.dressedZ_adjoint
        x_sq := D.dressedX_square
        z_sq := D.dressedZ_square
        anticommute := D.dressedX_anticommute_dressedZ }
    let hhamiltonian : H.operator.IsSymmetric :=
      (LinearMap.isSymmetric_iff_isSelfAdjoint H.operator).mpr
        H.operator_adjoint_eq_self
    let J : a → Operator (Qubit.QubitRegister iota) :=
      fun b ↦ toHermitianQubitOperator (jumpError b)
    let auxiliaryNontrivial : Nontrivial logical.AuxiliarySpace :=
      ThermalEncoding.PauliLikePair.auxiliarySpaceNontrivial logical
    let rhoBeta := @ThermalEncoding.PauliLikePair.physicalGibbsState
      (Qubit.QubitRegister iota) inferInstance inferInstance inferInstance logical
      auxiliaryNontrivial H.operator D.dressedZ_commute_hamiltonian.symm
      hhamiltonian beta
    lindbladDissipator J rhoBeta.toOperator = 0 →
      logical.x.IsSymmetric ∧
      logical.z.IsSymmetric ∧
      logical.x * logical.x = 1 ∧
      logical.z * logical.z = 1 ∧
      logical.x * logical.z = -(logical.z * logical.x) ∧
      Commute logical.x H.operator ∧
      Commute logical.z H.operator ∧
      DecoderDressedLogical.GoodSyndromeProtectedObservable D elementaryErrors ∧
      JumpProtected J D.dressedX (D.goodSyndromeProjector elementaryErrors) ∧
      JumpProtected J D.dressedZ (D.goodSyndromeProjector elementaryErrors) ∧
      ∃ Enc : QuantumChannel Qubit.QubitSpace (Qubit.QubitRegister iota),
        ∃ Dec : QuantumChannel (Qubit.QubitRegister iota) Qubit.QubitSpace,
          (∀ eta : DensityOperator Qubit.QubitSpace,
            Dec.mapDensity (Enc.mapDensity eta) = eta) ∧
          (∀ (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ)
              (_hdelta : 0 ≤ delta) (ht : 0 ≤ t),
            8 * t * lindbladDissipatorNorm J *
                Complex.re (D.badSyndromeGibbsWeight elementaryErrors rhoBeta) ≤
              delta →
            traceNorm
                (((finiteLindbladEvolutionChannel H.operator J hhamiltonian t
                      ht)
                    |>.mapDensity (Enc.mapDensity eta)).toOperator -
                  (Enc.mapDensity eta).toOperator) ≤ delta ∧
            traceNorm
                ((Dec.mapDensity
                    ((finiteLindbladEvolutionChannel H.operator J hhamiltonian t
                        ht)
                      |>.mapDensity (Enc.mapDensity eta))).toOperator -
                  eta.toOperator) ≤ delta) ∧
          (lindbladDissipatorNorm J *
                Complex.re (D.badSyndromeGibbsWeight elementaryErrors rhoBeta) = 0 →
            ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
              traceNorm
                  (((finiteLindbladEvolutionChannel H.operator J hhamiltonian t ht)
                      |>.mapDensity (Enc.mapDensity eta)).toOperator -
                    (Enc.mapDensity eta).toOperator) = 0 ∧
              traceNorm
                  ((Dec.mapDensity
                      ((finiteLindbladEvolutionChannel H.operator J hhamiltonian t ht)
                        |>.mapDensity (Enc.mapDensity eta))).toOperator -
                    eta.toOperator) = 0) := by
  dsimp only
  intro hstationary
  let logical : ThermalEncoding.PauliLikePair (Qubit.QubitRegister iota) :=
    { x := D.dressedX
      z := D.dressedZ
      x_symmetric :=
        (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedX).mpr D.dressedX_adjoint
      z_symmetric :=
        (LinearMap.isSymmetric_iff_isSelfAdjoint D.dressedZ).mpr D.dressedZ_adjoint
      x_sq := D.dressedX_square
      z_sq := D.dressedZ_square
      anticommute := D.dressedX_anticommute_dressedZ }
  letI : Nontrivial logical.AuxiliarySpace :=
    ThermalEncoding.PauliLikePair.auxiliarySpaceNontrivial logical
  let hhamiltonian : H.operator.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint H.operator).mpr
      H.operator_adjoint_eq_self
  let J : a → Operator (Qubit.QubitRegister iota) :=
    fun b ↦ toHermitianQubitOperator (jumpError b)
  let P := D.goodSyndromeProjector elementaryErrors
  let rhoBeta := logical.physicalGibbsState H.operator
    D.dressedZ_commute_hamiltonian.symm hhamiltonian beta
  have hprotectedX : JumpProtected J D.dressedX P := by
    intro b
    exact D.elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
      elementaryErrors (hjumpError b)
  have hprotectedZ : JumpProtected J D.dressedZ P := by
    intro b
    exact D.elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
      elementaryErrors (hjumpError b)
  have hmass : clbtGibbsTailMass P rhoBeta =
      Complex.re (D.badSyndromeGibbsWeight elementaryErrors rhoBeta) := by
    exact congrArg Complex.re
      (D.trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
        elementaryErrors rhoBeta)
  have hhorizon := protectedObservableStorageHorizon logical H.operator
    hhamiltonian beta J P
    (D.goodSyndromeProjector_isStarProjection elementaryErrors)
    (D.goodSyndromeProjector_commute_dressedX elementaryErrors)
    (D.goodSyndromeProjector_commute_dressedZ elementaryErrors)
    D.dressedX_commute_hamiltonian.symm
    D.dressedZ_commute_hamiltonian.symm
    (D.goodSyndromeProjector_commute_hamiltonian elementaryErrors)
    hprotectedX hprotectedZ hstationary
  refine ⟨logical.x_symmetric, logical.z_symmetric, logical.x_sq,
    logical.z_sq, logical.anticommute, D.dressedX_commute_hamiltonian,
    D.dressedZ_commute_hamiltonian,
    D.stabilizerGoodSyndromeProtectedObservable elementaryErrors,
    hprotectedX, hprotectedZ, ?_⟩
  simpa [logical, hhamiltonian, J, P, rhoBeta, hmass] using hhorizon

end QEC.Semantics
