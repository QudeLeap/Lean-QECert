import QEC.Coding.FiniteFieldMultiplication.SelfDualBasis

namespace QEC.Coding

/-- The fixed width-one binary embedding into the concrete field `F256`. -/
noncomputable def f256RMFEphi : ZMod 2 →ₗ[ZMod 2] F256 :=
  Algebra.linearMap (ZMod 2) F256

/-- The fixed width-one projection, weighted by the first self-dual basis vector. -/
noncomputable def f256RMFEpsi : F256 →ₗ[ZMod 2] ZMod 2 :=
  (Algebra.trace (ZMod 2) F256).comp (LinearMap.mulLeft (ZMod 2) (f256Alpha ^ 3))

/-- The linear embedding evaluates to the concrete algebra map. -/
theorem f256RMFEphi_apply (bit : ZMod 2) :
    f256RMFEphi bit = algebraMap (ZMod 2) F256 bit := by
  rw [f256RMFEphi, Algebra.linearMap_apply]

/-- The linear projection evaluates to the concrete weighted trace. -/
theorem f256RMFEpsi_apply (x : F256) :
    f256RMFEpsi x = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3 * x) := by
  rw [f256RMFEpsi, LinearMap.comp_apply, LinearMap.mulLeft_apply]

/-- The certified trace of the projection weight. -/
theorem f256TraceAlphaCubed :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) = 1 := by
  have hentry := congr_fun (congr_fun f256PolynomialTraceMatrix_eq 0) 3
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    f256PolynomialBasis_apply, f256PolynomialTraceGram] using hentry

/-- The certified trace needed for a concrete preimage of the bit one. -/
theorem f256TraceAlphaCubedSquare :
    Algebra.trace (ZMod 2) F256 ((f256Alpha ^ 3) ^ 2) = 1 := by
  have hentry := congr_fun (congr_fun f256PolynomialTraceMatrix_eq 3) 3
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    f256PolynomialBasis_apply, f256PolynomialTraceGram, pow_two] using hentry

/-- The concrete width-one embedding is injective. -/
theorem f256RMFEphi_injective : Function.Injective f256RMFEphi := by
  intro x y hxy
  exact (algebraMap (ZMod 2) F256).injective (by
    simpa only [f256RMFEphi_apply] using hxy)

/-- The weighted trace projection is a left inverse to the concrete embedding. -/
theorem f256RMFEpsi_phi (bit : ZMod 2) :
    f256RMFEpsi (f256RMFEphi bit) = bit := by
  calc
    f256RMFEpsi (f256RMFEphi bit) =
        bit * Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) := by
          rw [f256RMFEpsi_apply, f256RMFEphi_apply]
          simpa [Algebra.smul_def, mul_comm] using
            (Algebra.trace (ZMod 2) F256).map_smul bit (f256Alpha ^ 3)
    _ = bit := by rw [f256TraceAlphaCubed, mul_one]

/-- The concrete weighted trace projection reaches both binary values. -/
theorem f256RMFEpsi_surjective : Function.Surjective f256RMFEpsi := by
  intro bit
  exact ⟨f256RMFEphi bit, f256RMFEpsi_phi bit⟩

/-- The concrete maps satisfy the degree-three reverse-multiplication identity. -/
theorem f256RMFE_ternary_reverse_mul (x y z : ZMod 2) :
    f256RMFEpsi (f256RMFEphi x * f256RMFEphi y * f256RMFEphi z) = x * y * z := by
  calc
    f256RMFEpsi (f256RMFEphi x * f256RMFEphi y * f256RMFEphi z) =
        f256RMFEpsi (f256RMFEphi (x * y * z)) := by
          congr 1
          simp only [f256RMFEphi_apply]
          rw [← map_mul, ← map_mul]
    _ = x * y * z := f256RMFEpsi_phi (x * y * z)

end QEC.Coding
