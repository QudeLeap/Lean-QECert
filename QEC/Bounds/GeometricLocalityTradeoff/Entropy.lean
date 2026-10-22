import QEC.Bounds.GeometricLocalityTradeoff.Model
import QEC.Semantics.Entropy.Subadditivity
import QEC.Semantics.ErrorCorrection.ReferenceDecoupling
/-!
# BPT entropy consequences of finite-qudit erasure correctability

This internal module makes the finite-dimensional entropy step in the BPT
argument explicit.  It keeps concrete qudit erasure, reference decoupling,
and the triple-system reassociations visible in the theorem statements.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped TensorProduct

namespace BPTEntropy

open Semantics
open Semantics.DensityOperator

universe u

/-- The explicit reassociation from `A tensor (B tensor C)` to `B tensor (A tensor C)`. -/
noncomputable def abcToBac (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C] :
    UnitaryTransport (CompositeSystem A (CompositeSystem B C))
      (CompositeSystem B (CompositeSystem A C)) := by
  let e1 := (TensorProduct.assocIsometry Complex A B C).symm
  let e2 := (TensorProduct.commIsometry Complex A B).rTensor C
  let e3 := TensorProduct.assocIsometry Complex B A C
  let e := e1.trans (e2.trans e3)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        simpa [e, e1, e2, e3] using e.inner_map_map x y }

@[simp]
theorem abcToBac_apply_tmul (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (a : A) (b : B) (c : C) :
    abcToBac A B C (a ⊗ₜ[Complex] (b ⊗ₜ[Complex] c)) =
      b ⊗ₜ[Complex] (a ⊗ₜ[Complex] c) := by
  simp [abcToBac]

/--
Tracing `A` and `C` from `A tensor (B tensor C)` agrees with first
reassociating to `B tensor (A tensor C)` and tracing the right factor.
-/
theorem rightMarginal_leftMarginal_eq_rightMarginal_abcToBac
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C))) :
    rightMarginal (leftMarginal rho) =
      rightMarginal ((abcToBac A B C).conjDensity rho) := by
  apply DensityOperator.ext_toOperator
  let bA := stdOrthonormalBasis Complex A
  let bB := stdOrthonormalBasis Complex B
  let bC := stdOrthonormalBasis Complex C
  let basis := bA.tensorProduct (bB.tensorProduct bC)
  let Phi : Operator (CompositeSystem A (CompositeSystem B C)) →ₗ[Complex]
      Operator B :=
    (partialTraceRightRaw B C).comp
      ((partialTraceRightRaw (CompositeSystem B C) A).comp
        (tensorSwap A (CompositeSystem B C)).conjOperatorLinearMap)
  let Psi : Operator (CompositeSystem A (CompositeSystem B C)) →ₗ[Complex]
      Operator B :=
    (partialTraceRightRaw B (CompositeSystem A C)).comp
      (abcToBac A B C).conjOperatorLinearMap
  have hmaps : Phi = Psi := by
    apply QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    rintro ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩
    simp only [Phi, Psi, LinearMap.comp_apply, basis,
      OrthonormalBasis.tensorProduct_apply']
    change partialTraceRightRaw B C
        (partialTraceRightRaw (CompositeSystem B C) A
          ((tensorSwap A (CompositeSystem B C)).conjOperator
            (InnerProductSpace.rankOne Complex
              ((bA i) ⊗ₜ[Complex] ((bB j) ⊗ₜ[Complex] (bC k)))
              ((bA i') ⊗ₜ[Complex] ((bB j') ⊗ₜ[Complex] (bC k')))).toLinearMap)) =
      partialTraceRightRaw B (CompositeSystem A C)
        ((abcToBac A B C).conjOperator
          (InnerProductSpace.rankOne Complex
            ((bA i) ⊗ₜ[Complex] ((bB j) ⊗ₜ[Complex] (bC k)))
            ((bA i') ⊗ₜ[Complex] ((bB j') ⊗ₜ[Complex] (bC k')))).toLinearMap)
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    simp only [← UnitaryTransport.conjOperatorLinearMap_apply]
    rw [map_smul]
    simp only [UnitaryTransport.conjOperatorLinearMap_apply]
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [abcToBac_apply_tmul]
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [TensorProduct.inner_tmul]
    simp [smul_smul]
  exact LinearMap.congr_fun hmaps rho.toOperator

/-- A unitary transport sends a normalized rank-one density to the rank-one
density of its transported vector. -/
theorem conjDensity_pureDensity {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    U.conjDensity (pureDensity psi hpsi) =
      pureDensity (U psi) (by
        change ‖U.toLinearIsometryEquiv psi‖ ^ 2 = 1
        rw [U.toLinearIsometryEquiv.norm_map]
        exact hpsi) := by
  apply DensityOperator.ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator, pureDensity_toOperator,
    QuditSubsystem.conjOperator_rankOne, pureDensity_toOperator]

/-- The selected/reference state from #412 is the right marginal after its
explicit transport into `(M tensor Ref) tensor complement`. -/
theorem selectedReferenceMarginal_eq_rightMarginal_transport
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : QuditSubsystem q) (Ref : Type u)
    [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref] [FiniteQuantumSystem Ref]
    (omega : DensityOperator (CompositeSystem (Qudit.QuditRegister q) Ref)) :
    S.selectedReferenceMarginal Ref omega =
      rightMarginal ((S.selectedReferenceTransport Ref).conjDensity omega) :=
  rfl

set_option maxHeartbeats 800000 in
/--
The complementary marginal of the selected/reference transport is precisely
the concrete erasure channel applied after tracing out the untouched reference.
This is the heterogeneous `global register -> complement` bridge used by the
BPT correctable-region entropy identity.
-/
theorem leftMarginal_selectedReferenceTransport_eq_erasure
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : QuditSubsystem q) (Ref : Type u)
    [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref] [FiniteQuantumSystem Ref]
    (omega : DensityOperator (CompositeSystem (Qudit.QuditRegister q) Ref)) :
    leftMarginal ((S.selectedReferenceTransport Ref).conjDensity omega) =
      S.erasureChannelFromRegister.mapDensity (rightMarginal omega) := by
  apply DensityOperator.ext_toOperator
  let bGlobal := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let bRef := stdOrthonormalBasis Complex Ref
  let basis := bGlobal.tensorProduct bRef
  let Phi : Operator (CompositeSystem (Qudit.QuditRegister q) Ref) →ₗ[Complex]
      Operator S.complementSystem :=
    S.erasureChannelFromRegister.toLinearMap.comp
      (partialTraceRightRaw (Qudit.QuditRegister q) Ref)
  let Psi : Operator (CompositeSystem (Qudit.QuditRegister q) Ref) →ₗ[Complex]
      Operator S.complementSystem :=
    (partialTraceRightRaw S.complementSystem (CompositeSystem S.selectedSystem Ref)).comp
      ((tensorSwap (CompositeSystem S.selectedSystem Ref) S.complementSystem).conjOperatorLinearMap.comp
        (S.selectedReferenceTransport Ref).conjOperatorLinearMap)
  have hmaps : Phi = Psi := by
    apply QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    rintro ⟨x, r⟩ ⟨y, s⟩
    simp only [Phi, Psi, LinearMap.comp_apply, basis,
      OrthonormalBasis.tensorProduct_apply']
    change S.erasureChannelFromRegister
        (partialTraceRightRaw (Qudit.QuditRegister q) Ref
          (InnerProductSpace.rankOne Complex
            ((bGlobal x) ⊗ₜ[Complex] (bRef r))
            ((bGlobal y) ⊗ₜ[Complex] (bRef s))).toLinearMap) =
      partialTraceRightRaw S.complementSystem (CompositeSystem S.selectedSystem Ref)
        ((tensorSwap (CompositeSystem S.selectedSystem Ref) S.complementSystem).conjOperator
          ((S.selectedReferenceTransport Ref).conjOperator
            (InnerProductSpace.rankOne Complex
              ((bGlobal x) ⊗ₜ[Complex] (bRef r))
              ((bGlobal y) ⊗ₜ[Complex] (bRef s))).toLinearMap))
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    simp only [map_smul]
    rw [S.erasureChannelFromRegister_rankOne_basis]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [S.selectedReferenceTransport_apply_tmul]
    dsimp only [bGlobal]
    rw [S.registerFactorization_apply_basis x, S.registerFactorization_apply_basis y]
    simp only [S.selectedReferenceReordering_apply_tmul]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [TensorProduct.inner_tmul]
    simp [smul_smul, mul_comm]
  change partialTraceRightRaw S.complementSystem (CompositeSystem S.selectedSystem Ref)
      ((tensorSwap (CompositeSystem S.selectedSystem Ref) S.complementSystem).conjOperator
        ((S.selectedReferenceTransport Ref).conjOperator omega.toOperator)) =
    S.erasureChannelFromRegister
      (partialTraceRightRaw (Qudit.QuditRegister q) Ref omega.toOperator)
  exact (LinearMap.congr_fun hmaps omega.toOperator).symm

/--
For every code-supported finite density operator, exact recovery from the
concrete qudit erasure channel gives the BPT correctable-region identity
`S(M | complement M) = -S(M)`, written without a conditional-entropy field.
The quantified state is arbitrary; its spectral purification is used only for
the #412 reference-decoupling bridge.
-/
theorem erasure_correctable_entropy_identity
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hsupported : DensityOperator.SupportedOn C rho) :
    rho.vonNeumannEntropy -
        (S.erasureChannelFromRegister.mapDensity rho).vonNeumannEntropy =
      - (S.selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy := by
  let purification : DensityOperator.FinitePurification rho (Qudit.QuditRegister q) :=
    { vector := rho.spectralPurificationVector
      normSq_one := rho.spectralPurificationVector_normSq
      rightMarginal_eq := rho.rightMarginal_spectralPurification }
  have hfactor := S.erasureRecovery_implies_selectedReferenceMarginal_factorizes
    C recovery hcorrect rho hsupported (Qudit.QuditRegister q) purification
  let U := S.selectedReferenceTransport (Qudit.QuditRegister q)
  let psi := U rho.spectralPurificationVector
  have hpsi : ‖psi‖ ^ 2 = 1 := by
    change ‖U.toLinearIsometryEquiv rho.spectralPurificationVector‖ ^ 2 = 1
    rw [U.toLinearIsometryEquiv.norm_map]
    exact rho.spectralPurificationVector_normSq
  have hpure : U.conjDensity (spectralPurification rho) = pureDensity psi hpsi := by
    simpa [U, psi, spectralPurification] using
      conjDensity_pureDensity U rho.spectralPurificationVector
        rho.spectralPurificationVector_normSq
  have hfactorized :
      rightMarginal (U.conjDensity (spectralPurification rho)) =
        tensorDensity (S.selectedPartialTraceFromRegister.mapDensity rho)
          (leftMarginal (spectralPurification rho)) := by
    calc
      rightMarginal (U.conjDensity (spectralPurification rho)) =
          S.selectedReferenceMarginal (Qudit.QuditRegister q) (spectralPurification rho) := by
            exact (selectedReferenceMarginal_eq_rightMarginal_transport S
              (Qudit.QuditRegister q) (spectralPurification rho)).symm
      _ = tensorDensity (S.selectedPartialTraceFromRegister.mapDensity rho)
          (leftMarginal (spectralPurification rho)) := by
            simpa [purification, spectralPurification] using hfactor
  have hright_left :
      (rightMarginal (U.conjDensity (spectralPurification rho))).vonNeumannEntropy =
        (leftMarginal (U.conjDensity (spectralPurification rho))).vonNeumannEntropy := by
    rw [hpure]
    exact vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure psi hpsi
  have hleft_erasure :
      leftMarginal (U.conjDensity (spectralPurification rho)) =
        S.erasureChannelFromRegister.mapDensity rho := by
    rw [leftMarginal_selectedReferenceTransport_eq_erasure S (Qudit.QuditRegister q)
      (spectralPurification rho), rho.rightMarginal_spectralPurification_eq]
  have hfactor_entropy :
      (rightMarginal (U.conjDensity (spectralPurification rho))).vonNeumannEntropy =
        (S.selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy +
          (leftMarginal (spectralPurification rho)).vonNeumannEntropy := by
    rw [hfactorized, vonNeumannEntropy_tensorDensity]
  have herasure_entropy :
      (S.erasureChannelFromRegister.mapDensity rho).vonNeumannEntropy =
        (S.selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy +
      rho.vonNeumannEntropy := by
    rw [← hleft_erasure, ← hright_left, hfactor_entropy,
      rho.leftMarginal_spectralPurification_eq]
  linarith

/-- The source-faithful BPT-model specialization of
`erasure_correctable_entropy_identity`.  Its quantified density operator is
supported on the actual common-fixed commuting-projector code from #378. -/
theorem bpt_correctable_region_entropy_identity
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ) (region : Finset L.Site)
    (recovery : QuantumChannel (M.regionSubsystem region).complementSystem L.Register)
    (hcorrect : Correctable L.Register (M.regionSubsystem region).complementSystem M.codeSpace
      (M.regionSubsystem region).erasureChannelFromRegister recovery)
    (rho : DensityOperator L.Register)
    (hsupported : DensityOperator.SupportedOn M.codeSpace rho) :
    rho.vonNeumannEntropy -
        ((M.regionSubsystem region).erasureChannelFromRegister.mapDensity rho).vonNeumannEntropy =
      - ((M.regionSubsystem region).selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy := by
  exact erasure_correctable_entropy_identity (M.regionSubsystem region) M.codeSpace recovery
    hcorrect rho hsupported

/-- Swapping `A` and `B` twice restores every finite density operator. -/
theorem abcToBac_reverse_conjDensity
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C))) :
    (abcToBac B A C).conjDensity ((abcToBac A B C).conjDensity rho) = rho := by
  apply DensityOperator.ext_toOperator
  let bA := stdOrthonormalBasis Complex A
  let bB := stdOrthonormalBasis Complex B
  let bC := stdOrthonormalBasis Complex C
  let basis := bA.tensorProduct (bB.tensorProduct bC)
  let Phi : Operator (CompositeSystem A (CompositeSystem B C)) →ₗ[Complex]
      Operator (CompositeSystem A (CompositeSystem B C)) :=
    (abcToBac B A C).conjOperatorLinearMap.comp
      (abcToBac A B C).conjOperatorLinearMap
  let Psi : Operator (CompositeSystem A (CompositeSystem B C)) →ₗ[Complex]
      Operator (CompositeSystem A (CompositeSystem B C)) := LinearMap.id
  have hmaps : Phi = Psi := by
    apply QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    rintro ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩
    simp only [Phi, Psi, LinearMap.comp_apply, LinearMap.id_apply, basis,
      OrthonormalBasis.tensorProduct_apply']
    change (abcToBac B A C).conjOperator
        ((abcToBac A B C).conjOperator
          (InnerProductSpace.rankOne Complex
            ((bA i) ⊗ₜ[Complex] ((bB j) ⊗ₜ[Complex] (bC k)))
            ((bA i') ⊗ₜ[Complex] ((bB j') ⊗ₜ[Complex] (bC k')))).toLinearMap) = _
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [abcToBac_apply_tmul]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [abcToBac_apply_tmul]
  exact LinearMap.congr_fun hmaps rho.toOperator

/-- The `A` marginal is unchanged by the explicit `A`/`B` reassociation. -/
theorem rightMarginal_eq_rightMarginal_leftMarginal_abcToBac
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C))) :
    rightMarginal rho =
      rightMarginal (leftMarginal ((abcToBac A B C).conjDensity rho)) := by
  have hswap := rightMarginal_leftMarginal_eq_rightMarginal_abcToBac B A C
    ((abcToBac A B C).conjDensity rho)
  rw [abcToBac_reverse_conjDensity A B C rho] at hswap
  exact hswap.symm

/-- The `C` marginal is unchanged by the explicit `A`/`B` reassociation. -/
theorem leftMarginal_leftMarginal_eq_leftMarginal_leftMarginal_abcToBac
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C))) :
    leftMarginal (leftMarginal rho) =
      leftMarginal (leftMarginal ((abcToBac A B C).conjDensity rho)) := by
  apply DensityOperator.ext_toOperator
  let bA := stdOrthonormalBasis Complex A
  let bB := stdOrthonormalBasis Complex B
  let bC := stdOrthonormalBasis Complex C
  let basis := bA.tensorProduct (bB.tensorProduct bC)
  let Phi : Operator (CompositeSystem A (CompositeSystem B C)) →ₗ[Complex]
      Operator C :=
    (partialTraceRightRaw C B).comp
      ((tensorSwap B C).conjOperatorLinearMap.comp
        ((partialTraceRightRaw (CompositeSystem B C) A).comp
          (tensorSwap A (CompositeSystem B C)).conjOperatorLinearMap))
  let Psi : Operator (CompositeSystem A (CompositeSystem B C)) →ₗ[Complex]
      Operator C :=
    (partialTraceRightRaw C A).comp
      ((tensorSwap A C).conjOperatorLinearMap.comp
        ((partialTraceRightRaw (CompositeSystem A C) B).comp
          ((tensorSwap B (CompositeSystem A C)).conjOperatorLinearMap.comp
            (abcToBac A B C).conjOperatorLinearMap)))
  have hmaps : Phi = Psi := by
    apply QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    rintro ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩
    simp only [Phi, Psi, LinearMap.comp_apply, basis,
      OrthonormalBasis.tensorProduct_apply']
    change partialTraceRightRaw C B
        ((tensorSwap B C).conjOperator
          (partialTraceRightRaw (CompositeSystem B C) A
            ((tensorSwap A (CompositeSystem B C)).conjOperator
              (InnerProductSpace.rankOne Complex
                ((bA i) ⊗ₜ[Complex] ((bB j) ⊗ₜ[Complex] (bC k)))
                ((bA i') ⊗ₜ[Complex] ((bB j') ⊗ₜ[Complex] (bC k')))).toLinearMap))) =
      partialTraceRightRaw C A
        ((tensorSwap A C).conjOperator
          (partialTraceRightRaw (CompositeSystem A C) B
            ((tensorSwap B (CompositeSystem A C)).conjOperator
              ((abcToBac A B C).conjOperator
                (InnerProductSpace.rankOne Complex
                  ((bA i) ⊗ₜ[Complex] ((bB j) ⊗ₜ[Complex] (bC k)))
                  ((bA i') ⊗ₜ[Complex] ((bB j') ⊗ₜ[Complex] (bC k')))).toLinearMap))))
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    simp only [← UnitaryTransport.conjOperatorLinearMap_apply]
    rw [map_smul]
    simp only [UnitaryTransport.conjOperatorLinearMap_apply]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [map_smul]
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [abcToBac_apply_tmul]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    simp only [← UnitaryTransport.conjOperatorLinearMap_apply]
    rw [map_smul]
    simp only [UnitaryTransport.conjOperatorLinearMap_apply]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [map_smul]
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    simp [smul_smul, mul_comm]
  exact LinearMap.congr_fun hmaps rho.toOperator

/--
The exact `A`/`B`/`C` entropy calculation in the BPT argument.  The two
equalities are the separately derived correctability substitutions for `A`
and `B`; the proof below supplies precisely the two subadditivity inequalities
and their sum.
-/
theorem vonNeumannEntropy_abc_le_c_of_conditional_substitutions
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C)))
    (hA : rho.vonNeumannEntropy - (leftMarginal rho).vonNeumannEntropy =
      - (rightMarginal rho).vonNeumannEntropy)
    (hB : rho.vonNeumannEntropy -
        (leftMarginal ((abcToBac A B C).conjDensity rho)).vonNeumannEntropy =
      - (rightMarginal ((abcToBac A B C).conjDensity rho)).vonNeumannEntropy) :
    rho.vonNeumannEntropy <= (leftMarginal (leftMarginal rho)).vonNeumannEntropy := by
  have hsubBC := vonNeumannEntropy_subadditive_bipartite (leftMarginal rho)
  have hsubAC := vonNeumannEntropy_subadditive_bipartite
    (leftMarginal ((abcToBac A B C).conjDensity rho))
  rw [rightMarginal_leftMarginal_eq_rightMarginal_abcToBac A B C rho] at hsubBC
  rw [← rightMarginal_eq_rightMarginal_leftMarginal_abcToBac A B C rho] at hsubAC
  rw [← leftMarginal_leftMarginal_eq_leftMarginal_leftMarginal_abcToBac A B C rho] at hsubAC
  linarith

/-- The code-basis resolution of the full-code projector.  This turns the
normalized projector into a concrete finite density operator below. -/
theorem sum_code_basis_eq_projector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) :
    ∑ i : Fin C.dimension,
      (InnerProductSpace.rankOne Complex
        ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)
        ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)).toLinearMap =
      C.projector := by
  let b : OrthonormalBasis (Fin C.dimension) Complex C.carrier :=
    stdOrthonormalBasis Complex C.carrier
  let inclusion : C.carrier →ₗ[Complex] H := C.carrier.subtypeₗᵢ.toLinearMap
  have hAdj : LinearMap.adjoint inclusion = C.carrier.orthogonalProjection.toLinearMap := by
    apply LinearMap.ext
    intro x
    change (LinearMap.toContinuousLinearMap (LinearMap.adjoint inclusion)) x =
      C.carrier.orthogonalProjection x
    rw [LinearMap.adjoint_toContinuousLinearMap]
    change (ContinuousLinearMap.adjoint C.carrier.subtypeL) x =
      C.carrier.orthogonalProjection x
    rw [C.carrier.adjoint_subtypeL]
  have hProj : inclusion.comp (LinearMap.adjoint inclusion) = C.projector := by
    rw [hAdj]
    ext x
    rfl
  calc
    ∑ i : Fin C.dimension,
        (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)
          ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)).toLinearMap =
        ∑ i, (InnerProductSpace.rankOne Complex (inclusion (b i)) (inclusion (b i))).toLinearMap := by
          congr
    _ = inclusion.comp (LinearMap.adjoint inclusion) :=
      (comp_adjoint_eq_sum_rankOne b inclusion).symm
    _ = C.projector := hProj

/-- The canonical equal-weight pure purification of the full-code state on two
copies of the physical system. -/
noncomputable def codeReferenceVector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) : CompositeSystem H H :=
  ∑ i : Fin C.dimension,
    (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) •
      (((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H) ⊗ₜ[Complex]
        ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H))

/-- The equal-weight code purification is normalized when the code has positive
dimension; it is used to inherit positivity and trace one for `Lambda`. -/
theorem codeReferenceVector_normSq {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    ‖codeReferenceVector C‖ ^ 2 = 1 := by
  classical
  let e : Fin C.dimension → H := fun i =>
    ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)
  have he_inner (i j : Fin C.dimension) :
      inner Complex (e i) (e j) = if i = j then 1 else 0 :=
    (stdOrthonormalBasis Complex C.carrier).inner_eq_ite i j
  let a : Complex := Real.sqrt ((C.dimension : Real)⁻¹)
  have hpair (i j : Fin C.dimension) :
      inner Complex (a • (e i ⊗ₜ[Complex] e i)) (a • (e j ⊗ₜ[Complex] e j)) =
        if i = j then ((C.dimension : Real)⁻¹ : Complex) else 0 := by
    change inner Complex ((a • e i) ⊗ₜ[Complex] e i)
      ((a • e j) ⊗ₜ[Complex] e j) = _
    rw [TensorProduct.inner_tmul, inner_smul_left, inner_smul_right]
    simp only [he_inner, a, Complex.conj_ofReal]
    by_cases hij : i = j
    · subst j
      simp only [if_pos, mul_one]
      exact_mod_cast (show Real.sqrt ((C.dimension : Real)⁻¹) *
          Real.sqrt ((C.dimension : Real)⁻¹) = (C.dimension : Real)⁻¹ by
        simpa [pow_two] using Real.sq_sqrt (inv_nonneg.mpr (by positivity)))
    · simp_all
  have hinner :
      inner Complex (codeReferenceVector C) (codeReferenceVector C) =
        ∑ _ : Fin C.dimension, ((C.dimension : Real)⁻¹ : Complex) := by
    change inner Complex (∑ i, a • (e i ⊗ₜ[Complex] e i))
      (∑ i, a • (e i ⊗ₜ[Complex] e i)) = _
    rw [sum_inner]
    simp_rw [inner_sum, hpair]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner, map_sum]
  have hdim_ne : (C.dimension : Real) ≠ 0 := by exact_mod_cast hdim.ne'
  have h_re_inv : RCLike.re ((C.dimension : Complex)⁻¹) =
      (C.dimension : Real)⁻¹ := by
    change ((C.dimension : Complex)⁻¹).re = _
    rw [Complex.inv_re]
    norm_num [Complex.normSq_apply]
  change ∑ _ : Fin C.dimension, RCLike.re ((C.dimension : Complex)⁻¹) = 1
  rw [Finset.sum_congr rfl (fun _ _ => h_re_inv)]
  rw [Finset.sum_const]
  have hcard : (Finset.univ : Finset (Fin C.dimension)).card = C.dimension := by
    exact Fintype.card_fin C.dimension
  rw [hcard, nsmul_eq_mul]
  field_simp

/-- The normalized full-code-projector density operator `Lambda`, realized as
the physical marginal of `codeReferenceVector`. -/
noncomputable def normalizedCodeProjector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) : DensityOperator H :=
  rightMarginal (pureDensity (codeReferenceVector C) (codeReferenceVector_normSq C hdim))

/-- `Lambda` is exactly the full-code projector divided by the code dimension. -/
theorem normalizedCodeProjector_toOperator {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    (normalizedCodeProjector C hdim).toOperator =
      ((C.dimension : Real)⁻¹ : Complex) • C.projector := by
  classical
  unfold normalizedCodeProjector
  let e : Fin C.dimension → H := fun i =>
    ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)
  have he_inner (i j : Fin C.dimension) :
      inner Complex (e i) (e j) = if i = j then 1 else 0 :=
    (stdOrthonormalBasis Complex C.carrier).inner_eq_ite i j
  let a : Complex := Real.sqrt ((C.dimension : Real)⁻¹)
  change partialTraceRightRaw H H
    ((InnerProductSpace.rankOne Complex
      (∑ i, (a • e i) ⊗ₜ[Complex] e i)
      (∑ j, (a • e j) ⊗ₜ[Complex] e j)).toLinearMap) = _
  rw [rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  simp only [he_inner, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp
  simp_rw [smul_comm a ((starRingEnd Complex) a)]
  change ∑ x : Fin C.dimension, (starRingEnd Complex) a • a •
      (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap = _
  have hscalar : (starRingEnd Complex) a * a = ((C.dimension : Real)⁻¹ : Complex) := by
    change star (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) *
      (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) = _
    rw [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast (show Real.sqrt ((C.dimension : Real)⁻¹) *
        Real.sqrt ((C.dimension : Real)⁻¹) = (C.dimension : Real)⁻¹ by
      simpa [pow_two] using Real.sq_sqrt (inv_nonneg.mpr (by positivity)))
  calc
    ∑ x : Fin C.dimension, (starRingEnd Complex) a • a •
        (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap =
        ∑ x, ((C.dimension : Real)⁻¹ : Complex) •
          (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← mul_smul, hscalar]
    _ = ((C.dimension : Real)⁻¹ : Complex) •
        ∑ x, (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap :=
      (Finset.smul_sum).symm
    _ = ((C.dimension : Real)⁻¹ : Complex) • C.projector := by
      simp only [e]
      rw [sum_code_basis_eq_projector]

/-- The normalized full-code-projector density has image in the code carrier. -/
theorem normalizedCodeProjector_supportedOn {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    DensityOperator.SupportedOn C (normalizedCodeProjector C hdim) := by
  intro vector
  rw [normalizedCodeProjector_toOperator]
  exact C.carrier.smul_mem _ (C.projector_mem_carrier vector)

/-- The spectral entropy of a finite maximally mixed density operator.  This
is the bridge from the code-carrier marginal to `log2 (dim C)`. -/
theorem vonNeumannEntropy_eq_log_finrank_of_uniform_id {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H)
    (hoperator : rho.toOperator =
      ((Module.finrank Complex H : Real)⁻¹ : Complex) • LinearMap.id) :
    rho.vonNeumannEntropy = Real.logb 2 (Module.finrank Complex H : Real) := by
  let b := stdOrthonormalBasis Complex H
  rw [rho.vonNeumannEntropy_eq_basisMatrixSpectrum b]
  rw [hoperator]
  simp only [map_smul, LinearMap.toMatrix_id]
  rw [Matrix.smul_one_eq_diagonal]
  rw [Matrix.charpoly_diagonal]
  rw [Polynomial.roots_prod _ _ (by simp [Polynomial.X_sub_C_ne_zero])]
  simp
  exact card_mul_entropyTerm_reciprocal_eq_logb _ rho.finrank_pos

/-- A purification of `Lambda` whose reference is the code carrier itself.
Its physical marginal is the normalized full-code projector and its carrier
marginal is maximally mixed. -/
noncomputable def codeCarrierPurificationVector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) : CompositeSystem H C.carrier :=
  ∑ i : Fin C.dimension,
    (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) •
      (((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H) ⊗ₜ[Complex]
        (stdOrthonormalBasis Complex C.carrier i))

/-- The carrier-reference purification is normalized for a nonzero code. -/
theorem codeCarrierPurificationVector_normSq {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    ‖codeCarrierPurificationVector C‖ ^ 2 = 1 := by
  classical
  let b : OrthonormalBasis (Fin C.dimension) Complex C.carrier :=
    stdOrthonormalBasis Complex C.carrier
  let e : Fin C.dimension → H := fun i => (b i : H)
  let a : Complex := Real.sqrt ((C.dimension : Real)⁻¹)
  have hpair (i j : Fin C.dimension) :
      inner Complex (a • (e i ⊗ₜ[Complex] b i)) (a • (e j ⊗ₜ[Complex] b j)) =
        if i = j then ((C.dimension : Real)⁻¹ : Complex) else 0 := by
    change inner Complex ((a • e i) ⊗ₜ[Complex] b i)
      ((a • e j) ⊗ₜ[Complex] b j) = _
    rw [TensorProduct.inner_tmul, inner_smul_left, inner_smul_right]
    simp only [e, a, Complex.conj_ofReal]
    simp_rw [← C.carrier.coe_inner]
    simp only [b.inner_eq_ite]
    by_cases hij : i = j
    · subst j
      simp only [if_pos, mul_one]
      exact_mod_cast (show Real.sqrt ((C.dimension : Real)⁻¹) *
          Real.sqrt ((C.dimension : Real)⁻¹) = (C.dimension : Real)⁻¹ by
        simpa [pow_two] using Real.sq_sqrt (inv_nonneg.mpr (by positivity)))
    · simp_all
  have hinner :
      inner Complex (codeCarrierPurificationVector C) (codeCarrierPurificationVector C) =
        ∑ _ : Fin C.dimension, ((C.dimension : Real)⁻¹ : Complex) := by
    let f : Fin C.dimension → CompositeSystem H C.carrier := fun i =>
      (a • e i) ⊗ₜ[Complex] b i
    change inner Complex (∑ i, f i) (∑ i, f i) = _
    have hsum_inner (x : CompositeSystem H C.carrier) :
        inner Complex (∑ i, f i) x = ∑ i, inner Complex (f i) x :=
      sum_inner Finset.univ f x
    have hinter_sum (x : CompositeSystem H C.carrier) :
        inner Complex x (∑ i, f i) = ∑ i, inner Complex x (f i) :=
      inner_sum Finset.univ f x
    have hpairF (i j : Fin C.dimension) :
        inner Complex (f i) (f j) =
          if i = j then ((C.dimension : Real)⁻¹ : Complex) else 0 :=
      hpair i j
    calc
      inner Complex (∑ i, f i) (∑ i, f i) =
          ∑ i, inner Complex (f i) (∑ j, f j) := hsum_inner _
      _ = ∑ i, ∑ j, inner Complex (f i) (f j) := by
        simp_rw [hinter_sum]
      _ = ∑ _ : Fin C.dimension, ((C.dimension : Real)⁻¹ : Complex) := by
        simp_rw [hpairF]
        simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner, map_sum]
  have h_re_inv : RCLike.re ((C.dimension : Complex)⁻¹) =
      (C.dimension : Real)⁻¹ := by
    change ((C.dimension : Complex)⁻¹).re = _
    rw [Complex.inv_re]
    norm_num [Complex.normSq_apply]
  change ∑ _ : Fin C.dimension, RCLike.re ((C.dimension : Complex)⁻¹) = 1
  rw [Finset.sum_congr rfl (fun _ _ => h_re_inv)]
  rw [Finset.sum_const]
  have hcard : (Finset.univ : Finset (Fin C.dimension)).card = C.dimension := by
    exact Fintype.card_fin C.dimension
  rw [hcard, nsmul_eq_mul]
  have hdim_ne : (C.dimension : Real) ≠ 0 := by exact_mod_cast hdim.ne'
  field_simp

/-- The physical marginal of the carrier-reference purification is `Lambda`. -/
theorem rightMarginal_codeCarrierPurification_eq_normalizedCodeProjector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    rightMarginal (pureDensity (codeCarrierPurificationVector C)
      (codeCarrierPurificationVector_normSq C hdim)) = normalizedCodeProjector C hdim := by
  apply DensityOperator.ext_toOperator
  rw [normalizedCodeProjector_toOperator]
  let b : OrthonormalBasis (Fin C.dimension) Complex C.carrier :=
    stdOrthonormalBasis Complex C.carrier
  let e : Fin C.dimension → H := fun i => (b i : H)
  let a : Complex := Real.sqrt ((C.dimension : Real)⁻¹)
  change partialTraceRightRaw H C.carrier
    ((InnerProductSpace.rankOne Complex
      (∑ i, (a • e i) ⊗ₜ[Complex] b i)
      (∑ j, (a • e j) ⊗ₜ[Complex] b j)).toLinearMap) = _
  rw [rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  simp only [b.inner_eq_ite, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp
  simp_rw [smul_comm a ((starRingEnd Complex) a)]
  change ∑ x : Fin C.dimension, (starRingEnd Complex) a • a •
      (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap = _
  have hscalar : (starRingEnd Complex) a * a = ((C.dimension : Real)⁻¹ : Complex) := by
    change star (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) *
      (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) = _
    rw [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast (show Real.sqrt ((C.dimension : Real)⁻¹) *
        Real.sqrt ((C.dimension : Real)⁻¹) = (C.dimension : Real)⁻¹ by
      simpa [pow_two] using Real.sq_sqrt (inv_nonneg.mpr (by positivity)))
  calc
    ∑ x : Fin C.dimension, (starRingEnd Complex) a • a •
        (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap =
        ∑ x, ((C.dimension : Real)⁻¹ : Complex) •
          (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← mul_smul, hscalar]
    _ = ((C.dimension : Real)⁻¹ : Complex) •
        ∑ x, (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap :=
      (Finset.smul_sum).symm
    _ = ((C.dimension : Real)⁻¹ : Complex) • C.projector := by
      congr 1
      exact sum_code_basis_eq_projector C

/-- Swapping the carrier purification puts the code carrier on the left. -/
theorem tensorSwap_codeCarrierPurificationVector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) :
    tensorSwap H C.carrier (codeCarrierPurificationVector C) =
      ∑ i : Fin C.dimension,
        (stdOrthonormalBasis Complex C.carrier i) ⊗ₜ[Complex]
          ((Real.sqrt ((C.dimension : Real)⁻¹) : Complex) •
            ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)) := by
  unfold codeCarrierPurificationVector
  simp [map_sum, map_smul, tensorSwap_apply_tmul]

/-- The carrier marginal of the purification is the maximally mixed carrier
state, allowing its entropy to be evaluated by the spectral API. -/
theorem leftMarginal_codeCarrierPurification_toOperator {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    (leftMarginal (pureDensity (codeCarrierPurificationVector C)
      (codeCarrierPurificationVector_normSq C hdim))).toOperator =
      ((C.dimension : Real)⁻¹ : Complex) • LinearMap.id := by
  let b : OrthonormalBasis (Fin C.dimension) Complex C.carrier :=
    stdOrthonormalBasis Complex C.carrier
  let e : Fin C.dimension → H := fun i => (b i : H)
  let a : Complex := Real.sqrt ((C.dimension : Real)⁻¹)
  change partialTraceRightRaw C.carrier H
    ((tensorSwap H C.carrier).conjOperator
      ((InnerProductSpace.rankOne Complex (codeCarrierPurificationVector C)
        (codeCarrierPurificationVector C)).toLinearMap)) = _
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [tensorSwap_codeCarrierPurificationVector]
  change partialTraceRightRaw C.carrier H
    ((InnerProductSpace.rankOne Complex
      (∑ i, b i ⊗ₜ[Complex] (a • e i))
      (∑ j, b j ⊗ₜ[Complex] (a • e j))).toLinearMap) = _
  rw [rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  simp_rw [inner_smul_left, inner_smul_right]
  simp only [e]
  simp_rw [← C.carrier.coe_inner]
  simp only [b.inner_eq_ite]
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hscalar : (starRingEnd Complex) a * a = ((C.dimension : Real)⁻¹ : Complex) := by
    change star (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) *
      (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) = _
    rw [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast (show Real.sqrt ((C.dimension : Real)⁻¹) *
        Real.sqrt ((C.dimension : Real)⁻¹) = (C.dimension : Real)⁻¹ by
      simpa [pow_two] using Real.sq_sqrt (inv_nonneg.mpr (by positivity)))
  rw [hscalar, ← Finset.smul_sum]
  congr 1
  simpa only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.coe_id,
    Module.End.one_eq_id] using
    congrArg ContinuousLinearMap.toLinearMap b.sum_rankOne_eq_id

/-- The normalized full-code projector has entropy `log2 (dim C)`. -/
theorem normalizedCodeProjector_entropy_eq_log_dimension {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    (normalizedCodeProjector C hdim).vonNeumannEntropy =
      Real.logb 2 (C.dimension : Real) := by
  let psi := codeCarrierPurificationVector C
  let hpsi : ‖psi‖ ^ 2 = 1 := codeCarrierPurificationVector_normSq C hdim
  have hright := rightMarginal_codeCarrierPurification_eq_normalizedCodeProjector C hdim
  have hpure := vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure psi hpsi
  have huniform := vonNeumannEntropy_eq_log_finrank_of_uniform_id
    (leftMarginal (pureDensity psi hpsi)) (leftMarginal_codeCarrierPurification_toOperator C hdim)
  calc
    (normalizedCodeProjector C hdim).vonNeumannEntropy =
        (rightMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by
          rw [hright]
    _ = (leftMarginal (pureDensity psi hpsi)).vonNeumannEntropy := hpure
    _ = Real.logb 2 (Module.finrank Complex C.carrier : Real) := huniform
    _ = Real.logb 2 (C.dimension : Real) := rfl

/-- The #378 power-of-two code-dimension witness realizes the BPT convention
`S(Lambda) = log2(dim C) = k`. -/
theorem normalizedCodeProjector_entropy_eq_encodedQubits
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedCodeProjector M.codeSpace (by
      rw [parameter.codeDimension_eq_two_pow]
      exact pow_pos (by omega) _)).vonNeumannEntropy =
      (parameter.encodedQubits : Real) := by
  rw [normalizedCodeProjector_entropy_eq_log_dimension]
  rw [parameter.codeDimension_eq_two_pow]
  rw [Nat.cast_pow]
  change Real.logb 2 ((2 : Real) ^ parameter.encodedQubits) = _
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- A #378 encoded-qubit parameter forces the code carrier to be nontrivial. -/
theorem bptCodeDimension_pos
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    0 < M.codeSpace.dimension := by
  rw [parameter.codeDimension_eq_two_pow]
  exact pow_pos (by omega) _

/-- The normalized full-code-projector state used in the BPT entropy bound. -/
noncomputable def normalizedFullCodeProjector
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    DensityOperator L.Register :=
  normalizedCodeProjector M.codeSpace (bptCodeDimension_pos M parameter)

/-- The BPT normalized state is the full-code projector divided by `dim C`. -/
theorem normalizedFullCodeProjector_toOperator
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedFullCodeProjector M parameter).toOperator =
      ((M.codeSpace.dimension : Real)⁻¹ : Complex) • M.fullCodeProjector := by
  unfold normalizedFullCodeProjector
  simpa [BPTCommutingProjectorModel.fullCodeProjector] using
    normalizedCodeProjector_toOperator M.codeSpace
      (bptCodeDimension_pos M parameter)

/-- The BPT normalized full-code state is code-supported, so the universal
correctability identity applies to it without a pure-state restriction. -/
theorem normalizedFullCodeProjector_supportedOn
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    DensityOperator.SupportedOn M.codeSpace (normalizedFullCodeProjector M parameter) := by
  unfold normalizedFullCodeProjector
  exact normalizedCodeProjector_supportedOn M.codeSpace (bptCodeDimension_pos M parameter)

/-- The normalized full-code-projector state has entropy `log2 (dim C)`. -/
theorem normalizedFullCodeProjector_entropy_eq_log_dimension
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy =
      Real.logb 2 (M.codeSpace.dimension : Real) := by
  unfold normalizedFullCodeProjector
  exact normalizedCodeProjector_entropy_eq_log_dimension M.codeSpace
    (bptCodeDimension_pos M parameter)

/-- The #378 power-of-two convention turns `S(Lambda) = log2 (dim C)` into
the BPT encoded-qubit identity `S(Lambda) = k`. -/
theorem normalizedFullCodeProjector_entropy_eq_encodedQubits
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy =
      (parameter.encodedQubits : Real) := by
  unfold normalizedFullCodeProjector
  exact normalizedCodeProjector_entropy_eq_encodedQubits M parameter

/-- The BPT A/B/C entropy calculation followed by #411's concrete
finite-qudit entropy bound on the `C` register. -/
theorem vonNeumannEntropy_abc_le_c_selectedDimension
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (regionC : QuditSubsystem q)
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B regionC.selectedSystem)))
    (hA : rho.vonNeumannEntropy - (leftMarginal rho).vonNeumannEntropy =
      - (rightMarginal rho).vonNeumannEntropy)
    (hB : rho.vonNeumannEntropy -
        (leftMarginal ((abcToBac A B regionC.selectedSystem).conjDensity rho)).vonNeumannEntropy =
      - (rightMarginal ((abcToBac A B regionC.selectedSystem).conjDensity rho)).vonNeumannEntropy) :
    rho.vonNeumannEntropy <=
      ∑ i ∈ regionC.selected, Real.logb 2 (q i : Real) := by
  exact (vonNeumannEntropy_abc_le_c_of_conditional_substitutions A B regionC.selectedSystem
    rho hA hB).trans
      (regionC.vonNeumannEntropy_le_sum_log_selectedDimensions (leftMarginal (leftMarginal rho)))

/-!
## Concrete BPT `A`/`B`/`C` factorization

The four lemmas below are the coordinate-level interface between a pair of
disjoint lattice regions and the abstract `A tensor (B tensor C)` entropy
calculation above.  They are proved on computational matrix units, so the
reassociation remains visible rather than becoming an untracked isomorphism.
-/

namespace QuditSubsystem

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι -> Nat}

/-- The `C` subsystem left after the disjoint `A` and `B` coordinate regions. -/
def unionSubsystem (S T : QuditSubsystem q) : QuditSubsystem q where
  selected := S.selected ∪ T.selected

/-- Split a global computational label into its disjoint `A`, `B`, and `C`
coordinate components. -/
def splitABCLabel (S T : QuditSubsystem q) (labels : Qudit.Label q) :
    Qudit.Label S.selectedDimensions ×
      (Qudit.Label T.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions) :=
  (fun i => labels i, fun i => labels i, fun i => labels i)

def recombineABCLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions ×
      (Qudit.Label T.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions)) :
    Qudit.Label q :=
  fun i => if hiS : i ∈ S.selected then
    labels.1 ⟨i, hiS⟩
  else if hiT : i ∈ T.selected then
    labels.2.1 ⟨i, hiT⟩
  else labels.2.2 ⟨i, by
    simp only [unionSubsystem, Finset.mem_union, not_or]
    exact ⟨hiS, hiT⟩⟩

/-- Disjoint coordinate labels factor exactly into `A`, `B`, and their common
complement. -/
def abcLabelFactorization (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected) :
    Qudit.Label q ≃ Qudit.Label S.selectedDimensions ×
      (Qudit.Label T.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions) where
  toFun := splitABCLabel S T
  invFun := recombineABCLabel S T
  left_inv := by
    intro labels
    funext i
    by_cases hiS : i ∈ S.selected
    · simp [splitABCLabel, recombineABCLabel, hiS]
    · by_cases hiT : i ∈ T.selected
      · simp [splitABCLabel, recombineABCLabel, hiS, hiT]
      · simp [splitABCLabel, recombineABCLabel, hiS, hiT]
  right_inv := by
    rintro ⟨selectedS, selectedT, complement⟩
    apply Prod.ext
    · funext i
      simp [splitABCLabel, recombineABCLabel]
    · apply Prod.ext
      · funext i
        have hiS : (i : ι) ∉ S.selected := by
          intro hmem
          exact (Finset.disjoint_left.mp hST) hmem i.property
        simp [splitABCLabel, recombineABCLabel, hiS]
      · funext i
        have hiS : (i : ι) ∉ S.selected := by
          intro hmem
          exact i.property (by simp [unionSubsystem, hmem])
        have hiT : (i : ι) ∉ T.selected := by
          intro hmem
          exact i.property (by simp [unionSubsystem, hmem])
        simp [splitABCLabel, recombineABCLabel, hiS, hiT]

/-- The concrete global-register unitary transport into `A tensor (B tensor C)`. -/
noncomputable def abcFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    UnitaryTransport (Qudit.QuditRegister q)
      (CompositeSystem S.selectedSystem
        (CompositeSystem T.selectedSystem (unionSubsystem S T).complementSystem)) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let selectedSBasis := EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
  let selectedTBasis := EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
  let complementBasis :=
    EuclideanSpace.basisFun (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
  let targetBasis := selectedSBasis.tensorProduct (selectedTBasis.tensorProduct complementBasis)
  let U := sourceBasis.equiv targetBasis (abcLabelFactorization S T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- Computational-basis action of the explicit `A`/`B`/`C` factorization. -/
theorem abcFactorization_apply_basis (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label q) :
    abcFactorization S T hST (EuclideanSpace.basisFun (Qudit.Label q) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (splitABCLabel S T labels).1) ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
        (splitABCLabel S T labels).2.1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
        (splitABCLabel S T labels).2.2)) := by
  dsimp [abcFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [abcLabelFactorization]

/-- Split the complement of `A` into `B` and `C`. -/
def splitComplementABCLabel (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label S.complementDimensions) :
    Qudit.Label T.selectedDimensions ×
      Qudit.Label (unionSubsystem S T).complementDimensions :=
  (fun i => labels ⟨i, by
      intro hiS
      exact (Finset.disjoint_left.mp hST) hiS i.property⟩,
    fun i => labels ⟨i, by
      exact fun hiS => i.property (by simp [unionSubsystem, hiS])⟩)

def recombineComplementABCLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label T.selectedDimensions ×
      Qudit.Label (unionSubsystem S T).complementDimensions) :
    Qudit.Label S.complementDimensions :=
  fun i => if hiT : (i : ι) ∈ T.selected then
    labels.1 ⟨i, hiT⟩
  else labels.2 ⟨i, by
    simp only [unionSubsystem, Finset.mem_union, not_or]
    exact ⟨i.property, hiT⟩⟩

/-- The complement of `A` factors concretely as `B tensor C`. -/
def complementABCLabelFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    Qudit.Label S.complementDimensions ≃
      Qudit.Label T.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions where
  toFun := splitComplementABCLabel S T hST
  invFun := recombineComplementABCLabel S T
  left_inv := by
    intro labels
    funext i
    by_cases hiT : (i : ι) ∈ T.selected
    · simp [splitComplementABCLabel, recombineComplementABCLabel, hiT]
    · simp [splitComplementABCLabel, recombineComplementABCLabel, hiT]
  right_inv := by
    rintro ⟨selectedT, complement⟩
    apply Prod.ext
    · funext i
      have hiS : (i : ι) ∉ S.selected := by
        intro hmem
        exact (Finset.disjoint_left.mp hST) hmem i.property
      simp [splitComplementABCLabel, recombineComplementABCLabel]
    · funext i
      have hiS : (i : ι) ∉ S.selected := by
        intro hmem
        exact i.property (by simp [unionSubsystem, hmem])
      have hiT : (i : ι) ∉ T.selected := by
        intro hmem
        exact i.property (by simp [unionSubsystem, hmem])
      simp [splitComplementABCLabel, recombineComplementABCLabel, hiT]

/-- The unitary transport from the concrete complement of `A` to `B tensor C`. -/
noncomputable def complementABCFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    UnitaryTransport S.complementSystem
      (CompositeSystem T.selectedSystem (unionSubsystem S T).complementSystem) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
  let selectedTBasis := EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
  let complementBasis :=
    EuclideanSpace.basisFun (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
  let targetBasis := selectedTBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis (complementABCLabelFactorization S T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

theorem complementABCFactorization_apply_basis (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label S.complementDimensions) :
    complementABCFactorization S T hST
      (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
        (splitComplementABCLabel S T hST labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
        (splitComplementABCLabel S T hST labels).2) := by
  dsimp [complementABCFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [complementABCLabelFactorization]

theorem splitComplementABCLabel_splitLabel (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label q) :
    splitComplementABCLabel S T hST (S.splitLabel labels).2 =
      (splitABCLabel S T labels).2 := by
  apply Prod.ext <;> funext i <;> rfl

/- The `A` selected marginal of the explicit triple transport is the concrete
selected-coordinate partial trace. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem rightMarginal_abcFactorization_eq_selectedPartialTraceFromRegister
    (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected)
    (rho : DensityOperator (Qudit.QuditRegister q)) :
    rightMarginal ((abcFactorization S T hST).conjDensity rho) =
      S.selectedPartialTraceFromRegister.mapDensity rho := by
  apply DensityOperator.ext_toOperator
  let basis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let Phi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator S.selectedSystem :=
    (partialTraceRightRaw S.selectedSystem
      (CompositeSystem T.selectedSystem (unionSubsystem S T).complementSystem)).comp
      (abcFactorization S T hST).conjOperatorLinearMap
  let Psi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator S.selectedSystem :=
    S.selectedPartialTraceFromRegister.toLinearMap
  have hmaps : Phi = Psi := by
    apply Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    intro x y
    simp only [Phi, Psi, LinearMap.comp_apply]
    change partialTraceRightRaw S.selectedSystem
        (CompositeSystem T.selectedSystem (unionSubsystem S T).complementSystem)
        ((abcFactorization S T hST).conjOperator
          (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap) =
      S.selectedPartialTraceFromRegister
        (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    rw [abcFactorization_apply_basis S T hST x, abcFactorization_apply_basis S T hST y]
    rw [Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [TensorProduct.inner_tmul]
    change _ = partialTraceRightRaw S.selectedSystem S.complementSystem
      (S.registerFactorization.conjOperator
        (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap)
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    rw [S.registerFactorization_apply_basis x, S.registerFactorization_apply_basis y]
    rw [Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    have hinner :
        inner Complex
          ((EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
            (splitABCLabel S T y).2.1) ⊗ₜ[Complex]
            (EuclideanSpace.basisFun
              (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
              (splitABCLabel S T y).2.2))
          ((EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
            (splitABCLabel S T x).2.1) ⊗ₜ[Complex]
            (EuclideanSpace.basisFun
              (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
              (splitABCLabel S T x).2.2)) =
          inner Complex
            (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
              (S.splitLabel y).2)
            (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
              (S.splitLabel x).2) := by
      rw [← (complementABCFactorization S T hST).map_inner]
      rw [complementABCFactorization_apply_basis,
        complementABCFactorization_apply_basis]
      rw [splitComplementABCLabel_splitLabel, splitComplementABCLabel_splitLabel]
    rw [← TensorProduct.inner_tmul]
    rw [hinner]
    rfl
  exact LinearMap.congr_fun hmaps rho.toOperator

/- The complementary `BC` marginal of the triple transport is `A`'s concrete
erasure channel, followed by the explicit `B tensor C` transport. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem leftMarginal_abcFactorization_eq_complementABCErasure
    (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected)
    (rho : DensityOperator (Qudit.QuditRegister q)) :
    leftMarginal ((abcFactorization S T hST).conjDensity rho) =
      (complementABCFactorization S T hST).conjDensity
        (S.erasureChannelFromRegister.mapDensity rho) := by
  apply DensityOperator.ext_toOperator
  let basis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let BC := CompositeSystem T.selectedSystem (unionSubsystem S T).complementSystem
  let Phi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator BC :=
    (partialTraceRightRaw BC S.selectedSystem).comp
      ((tensorSwap S.selectedSystem BC).conjOperatorLinearMap.comp
        (abcFactorization S T hST).conjOperatorLinearMap)
  let Psi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator BC :=
    (complementABCFactorization S T hST).conjOperatorLinearMap.comp
      S.erasureChannelFromRegister.toLinearMap
  have hmaps : Phi = Psi := by
    apply Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    intro x y
    simp only [Phi, Psi, LinearMap.comp_apply]
    change partialTraceRightRaw BC S.selectedSystem
        ((tensorSwap S.selectedSystem BC).conjOperator
          ((abcFactorization S T hST).conjOperator
            (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap)) =
      (complementABCFactorization S T hST).conjOperator
        (S.erasureChannelFromRegister
          (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap)
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    rw [abcFactorization_apply_basis S T hST x, abcFactorization_apply_basis S T hST y]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [S.erasureChannelFromRegister_rankOne_basis x y]
    change _ = (complementABCFactorization S T hST).conjOperatorLinearMap
      (inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel y).1)
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel x).1) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
            (S.splitLabel x).2)
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
            (S.splitLabel y).2)).toLinearMap)
    rw [map_smul]
    rw [UnitaryTransport.conjOperatorLinearMap_apply]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    have hcomp_x := complementABCFactorization_apply_basis S T hST (S.splitLabel x).2
    have hcomp_y := complementABCFactorization_apply_basis S T hST (S.splitLabel y).2
    rw [hcomp_x, hcomp_y]
    rw [splitComplementABCLabel_splitLabel, splitComplementABCLabel_splitLabel]
    rfl
  exact LinearMap.congr_fun hmaps rho.toOperator

/-- Split the complement of `B` into `A` and `C`. -/
def splitComplementBACLabel (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label T.complementDimensions) :
    Qudit.Label S.selectedDimensions ×
      Qudit.Label (unionSubsystem S T).complementDimensions :=
  (fun i => labels ⟨i, by
      intro hiT
      exact (Finset.disjoint_left.mp hST) i.property hiT⟩,
    fun i => labels ⟨i, by
      exact fun hiT => i.property (by simp [unionSubsystem, hiT])⟩)

def recombineComplementBACLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions ×
      Qudit.Label (unionSubsystem S T).complementDimensions) :
    Qudit.Label T.complementDimensions :=
  fun i => if hiS : (i : ι) ∈ S.selected then
    labels.1 ⟨i, hiS⟩
  else labels.2 ⟨i, by
    simp only [unionSubsystem, Finset.mem_union, not_or]
    exact ⟨hiS, i.property⟩⟩

/-- The complement of `B` factors concretely as `A tensor C`. -/
def complementBACLabelFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    Qudit.Label T.complementDimensions ≃
      Qudit.Label S.selectedDimensions ×
        Qudit.Label (unionSubsystem S T).complementDimensions where
  toFun := splitComplementBACLabel S T hST
  invFun := recombineComplementBACLabel S T
  left_inv := by
    intro labels
    funext i
    by_cases hiS : (i : ι) ∈ S.selected
    · simp [splitComplementBACLabel, recombineComplementBACLabel, hiS]
    · simp [splitComplementBACLabel, recombineComplementBACLabel, hiS]
  right_inv := by
    rintro ⟨selectedS, complement⟩
    apply Prod.ext
    · funext i
      have hiT : (i : ι) ∉ T.selected := by
        intro hmem
        exact (Finset.disjoint_left.mp hST) i.property hmem
      simp [splitComplementBACLabel, recombineComplementBACLabel]
    · funext i
      have hiS : (i : ι) ∉ S.selected := by
        intro hmem
        exact i.property (by simp [unionSubsystem, hmem])
      have hiT : (i : ι) ∉ T.selected := by
        intro hmem
        exact i.property (by simp [unionSubsystem, hmem])
      simp [splitComplementBACLabel, recombineComplementBACLabel, hiS]

/-- The unitary transport from the concrete complement of `B` to `A tensor C`. -/
noncomputable def complementBACFactorization (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) :
    UnitaryTransport T.complementSystem
      (CompositeSystem S.selectedSystem (unionSubsystem S T).complementSystem) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
  let selectedSBasis := EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
  let complementBasis :=
    EuclideanSpace.basisFun (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
  let targetBasis := selectedSBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis (complementBACLabelFactorization S T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

theorem complementBACFactorization_apply_basis (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label T.complementDimensions) :
    complementBACFactorization S T hST
      (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (splitComplementBACLabel S T hST labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
        (splitComplementBACLabel S T hST labels).2) := by
  dsimp [complementBACFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [complementBACLabelFactorization]

theorem splitComplementBACLabel_splitLabel (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label q) :
    splitComplementBACLabel S T hST (T.splitLabel labels).2 =
      ((splitABCLabel S T labels).1, (splitABCLabel S T labels).2.2) := by
  apply Prod.ext <;> funext i <;> rfl

/- The `B` selected marginal after the explicit `A`/`B` reassociation is the
concrete selected-coordinate partial trace for `B`. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem rightMarginal_bacOfAbcFactorization_eq_selectedPartialTraceFromRegister
    (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected)
    (rho : DensityOperator (Qudit.QuditRegister q)) :
    rightMarginal
      ((abcToBac S.selectedSystem T.selectedSystem (unionSubsystem S T).complementSystem).conjDensity
        ((abcFactorization S T hST).conjDensity rho)) =
      T.selectedPartialTraceFromRegister.mapDensity rho := by
  apply DensityOperator.ext_toOperator
  let basis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let C := (unionSubsystem S T).complementSystem
  let Phi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator T.selectedSystem :=
    (partialTraceRightRaw T.selectedSystem (CompositeSystem S.selectedSystem C)).comp
      ((abcToBac S.selectedSystem T.selectedSystem C).conjOperatorLinearMap.comp
        (abcFactorization S T hST).conjOperatorLinearMap)
  let Psi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator T.selectedSystem :=
    T.selectedPartialTraceFromRegister.toLinearMap
  have hmaps : Phi = Psi := by
    apply Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    intro x y
    simp only [Phi, Psi, LinearMap.comp_apply]
    change partialTraceRightRaw T.selectedSystem (CompositeSystem S.selectedSystem C)
        ((abcToBac S.selectedSystem T.selectedSystem C).conjOperator
          ((abcFactorization S T hST).conjOperator
            (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap)) =
      T.selectedPartialTraceFromRegister
        (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    rw [abcFactorization_apply_basis S T hST x, abcFactorization_apply_basis S T hST y]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    simp only [abcToBac_apply_tmul]
    rw [Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [TensorProduct.inner_tmul]
    change _ = partialTraceRightRaw T.selectedSystem T.complementSystem
      (T.registerFactorization.conjOperator
        (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap)
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    rw [T.registerFactorization_apply_basis x, T.registerFactorization_apply_basis y]
    rw [Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    have hinner :
        inner Complex
          ((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
            (splitABCLabel S T y).1) ⊗ₜ[Complex]
            (EuclideanSpace.basisFun (Qudit.Label (unionSubsystem S T).complementDimensions)
              Complex (splitABCLabel S T y).2.2))
          ((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
            (splitABCLabel S T x).1) ⊗ₜ[Complex]
            (EuclideanSpace.basisFun (Qudit.Label (unionSubsystem S T).complementDimensions)
              Complex (splitABCLabel S T x).2.2)) =
          inner Complex
            (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
              (T.splitLabel y).2)
            (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
              (T.splitLabel x).2) := by
      rw [← (complementBACFactorization S T hST).map_inner]
      rw [complementBACFactorization_apply_basis,
        complementBACFactorization_apply_basis]
      rw [splitComplementBACLabel_splitLabel, splitComplementBACLabel_splitLabel]
    rw [← TensorProduct.inner_tmul]
    rw [hinner]
    rfl
  exact LinearMap.congr_fun hmaps rho.toOperator

/- The complementary `AC` marginal after reassociation is `B`'s concrete
erasure channel, followed by the explicit `A tensor C` transport. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem leftMarginal_bacOfAbcFactorization_eq_complementBACErasure
    (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected)
    (rho : DensityOperator (Qudit.QuditRegister q)) :
    leftMarginal ((abcToBac S.selectedSystem T.selectedSystem
      (unionSubsystem S T).complementSystem).conjDensity
        ((abcFactorization S T hST).conjDensity rho)) =
      (complementBACFactorization S T hST).conjDensity
        (T.erasureChannelFromRegister.mapDensity rho) := by
  apply DensityOperator.ext_toOperator
  let basis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let AC := CompositeSystem S.selectedSystem (unionSubsystem S T).complementSystem
  let Phi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator AC :=
    (partialTraceRightRaw AC T.selectedSystem).comp
      ((tensorSwap T.selectedSystem AC).conjOperatorLinearMap.comp
        ((abcToBac S.selectedSystem T.selectedSystem
          (unionSubsystem S T).complementSystem).conjOperatorLinearMap.comp
          (abcFactorization S T hST).conjOperatorLinearMap))
  let Psi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator AC :=
    (complementBACFactorization S T hST).conjOperatorLinearMap.comp
      T.erasureChannelFromRegister.toLinearMap
  have hmaps : Phi = Psi := by
    apply Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    intro x y
    simp only [Phi, Psi, LinearMap.comp_apply]
    change partialTraceRightRaw AC T.selectedSystem
        ((tensorSwap T.selectedSystem AC).conjOperator
          ((abcToBac S.selectedSystem T.selectedSystem
            (unionSubsystem S T).complementSystem).conjOperator
            ((abcFactorization S T hST).conjOperator
              (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap))) =
      (complementBACFactorization S T hST).conjOperator
        (T.erasureChannelFromRegister
          (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap)
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    rw [abcFactorization_apply_basis S T hST x, abcFactorization_apply_basis S T hST y]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    simp only [abcToBac_apply_tmul]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [T.erasureChannelFromRegister_rankOne_basis x y]
    change _ = (complementBACFactorization S T hST).conjOperatorLinearMap
      (inner Complex
        (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
          (T.splitLabel y).1)
        (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
          (T.splitLabel x).1) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (T.splitLabel x).2)
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (T.splitLabel y).2)).toLinearMap)
    rw [map_smul]
    rw [UnitaryTransport.conjOperatorLinearMap_apply]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    have hcomp_x := complementBACFactorization_apply_basis S T hST (T.splitLabel x).2
    have hcomp_y := complementBACFactorization_apply_basis S T hST (T.splitLabel y).2
    rw [hcomp_x, hcomp_y]
    rw [splitComplementBACLabel_splitLabel, splitComplementBACLabel_splitLabel]
    rfl
  exact LinearMap.congr_fun hmaps rho.toOperator

end QuditSubsystem

/-- The source-faithful BPT entropy inequality for the normalized full-code
projector.  `A` and `B` are concrete disjoint lattice regions with actual
recovery maps for their `erasureChannelFromRegister` channels.  Their two
correctability identities are transported into the explicit `A tensor (B
tensor C)` calculation, whose two subadditivity steps bound `S(Lambda)` by the
heterogeneous local-dimension logarithm sum on `C`. -/
theorem bpt_normalizedFullCodeProjector_entropy_le_complement_log_dimensions
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (A B : Finset L.Site) (hdisjoint : Disjoint A B)
    (recoveryA : QuantumChannel (M.regionSubsystem A).complementSystem L.Register)
    (hcorrectA : Correctable L.Register (M.regionSubsystem A).complementSystem M.codeSpace
      (M.regionSubsystem A).erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel (M.regionSubsystem B).complementSystem L.Register)
    (hcorrectB : Correctable L.Register (M.regionSubsystem B).complementSystem M.codeSpace
      (M.regionSubsystem B).erasureChannelFromRegister recoveryB) :
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy <=
      ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem (M.regionSubsystem A)
        (M.regionSubsystem B)).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) := by
  let S := M.regionSubsystem A
  let T := M.regionSubsystem B
  let C := _root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem S T
  have hST : Disjoint S.selected T.selected := by
    simpa [S, T] using hdisjoint
  let Lambda := normalizedFullCodeProjector M parameter
  let rhoABC := (QuditSubsystem.abcFactorization S T hST).conjDensity Lambda
  have hLambdaSupported : DensityOperator.SupportedOn M.codeSpace Lambda := by
    dsimp [Lambda]
    exact normalizedFullCodeProjector_supportedOn M parameter
  have hAglobal := bpt_correctable_region_entropy_identity M A recoveryA hcorrectA Lambda
    hLambdaSupported
  have hBglobal := bpt_correctable_region_entropy_identity M B recoveryB hcorrectB Lambda
    hLambdaSupported
  have hA : rhoABC.vonNeumannEntropy - (leftMarginal rhoABC).vonNeumannEntropy =
      - (rightMarginal rhoABC).vonNeumannEntropy := by
    dsimp [rhoABC]
    rw [QuditSubsystem.leftMarginal_abcFactorization_eq_complementABCErasure]
    rw [QuditSubsystem.rightMarginal_abcFactorization_eq_selectedPartialTraceFromRegister]
    rw [vonNeumannEntropy_conjDensity]
    rw [vonNeumannEntropy_conjDensity]
    exact hAglobal
  have hB : rhoABC.vonNeumannEntropy -
      (leftMarginal ((abcToBac S.selectedSystem T.selectedSystem C.complementSystem).conjDensity rhoABC)).vonNeumannEntropy =
      - (rightMarginal ((abcToBac S.selectedSystem T.selectedSystem C.complementSystem).conjDensity rhoABC)).vonNeumannEntropy := by
    dsimp [rhoABC]
    rw [QuditSubsystem.leftMarginal_bacOfAbcFactorization_eq_complementBACErasure]
    rw [QuditSubsystem.rightMarginal_bacOfAbcFactorization_eq_selectedPartialTraceFromRegister]
    rw [vonNeumannEntropy_conjDensity, vonNeumannEntropy_conjDensity]
    exact hBglobal
  have hABC : rhoABC.vonNeumannEntropy <=
      (leftMarginal (leftMarginal rhoABC)).vonNeumannEntropy :=
    vonNeumannEntropy_abc_le_c_of_conditional_substitutions S.selectedSystem T.selectedSystem
      C.complementSystem rhoABC hA hB
  have hC := Qudit.vonNeumannEntropy_le_sum_log_registerDimensions C.complementDimensions
    (leftMarginal (leftMarginal rhoABC))
  calc
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy = Lambda.vonNeumannEntropy := by
      rfl
    _ = rhoABC.vonNeumannEntropy := by
      dsimp [rhoABC]
      rw [vonNeumannEntropy_conjDensity]
    _ <= (leftMarginal (leftMarginal rhoABC)).vonNeumannEntropy := hABC
    _ <= ∑ i : C.ComplementCoordinates, Real.logb 2 (L.localDimension i : Real) := hC

/-- The #378 power-of-two convention turns the normalized-state BPT entropy
bound into the encoded-qubit inequality `k <= log dim(C)`. -/
theorem bpt_encodedQubits_le_complement_log_dimensions
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (A B : Finset L.Site) (hdisjoint : Disjoint A B)
    (recoveryA : QuantumChannel (M.regionSubsystem A).complementSystem L.Register)
    (hcorrectA : Correctable L.Register (M.regionSubsystem A).complementSystem M.codeSpace
      (M.regionSubsystem A).erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel (M.regionSubsystem B).complementSystem L.Register)
    (hcorrectB : Correctable L.Register (M.regionSubsystem B).complementSystem M.codeSpace
      (M.regionSubsystem B).erasureChannelFromRegister recoveryB) :
    (parameter.encodedQubits : Real) <=
      ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem (M.regionSubsystem A)
        (M.regionSubsystem B)).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) := by
  calc
    (parameter.encodedQubits : Real) = (normalizedFullCodeProjector M parameter).vonNeumannEntropy :=
      (normalizedFullCodeProjector_entropy_eq_encodedQubits M parameter).symm
    _ <= ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem
        (M.regionSubsystem A) (M.regionSubsystem B)).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) :=
      bpt_normalizedFullCodeProjector_entropy_le_complement_log_dimensions M parameter A B
        hdisjoint recoveryA hcorrectA recoveryB hcorrectB

end BPTEntropy
end Bounds
end QEC
