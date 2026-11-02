import QEC.Semantics.Dynamics.ProtectedObservableDecay

/-!
# Protected-observable storage horizons

The abstract CLBT displacement estimate gives encoded and decoded storage
horizons with the exact factor eight and an explicit all-time zero-rate branch.
-/

noncomputable section

namespace QEC.Semantics

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

end QEC.Semantics
