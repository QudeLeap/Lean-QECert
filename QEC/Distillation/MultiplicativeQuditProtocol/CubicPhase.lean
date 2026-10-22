import QEC.Distillation.MultiplicativeQuditProtocol.CCZIntertwining
import QEC.Distillation.PrimeQuditProtocol.CubicCSS

/-!
# Cubic phases for arbitrary binary-linear functionals

Ngu24's binary conversion uses `U_f |x,y,z⟩ = (-1)^(f(x*y*z)) |x,y,z⟩`,
where `f` is an arbitrary `F₂`-linear functional, not necessarily the trace.
The field-valued shortened-coset identity proves this action for the same
actual encoder. The diagonal linear algebra is reused from its existing
label-generic implementation; no prime-field hypothesis is imposed here.
-/

noncomputable section

namespace QEC.Distillation.Ngu24MultiplicativeCCZ

open Coding Semantics Ngu24MultiplicativeCSS
open scoped BigOperators

universe u

variable {F J I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype J] [DecidableEq J]

/-- The literal sum of cubic exponents on a chosen set of three-tag sites. -/
def taggedCubicPhaseExponent (sites : Finset J)
    (label : TaggedThreeCopyRegisterLabel F J) : F :=
  ∑ j ∈ sites, label (.first, j) * label (.second, j) * label (.third, j)

/-- The sign prescribed by the source's binary-linear functional. -/
def taggedCubicPhaseAmplitude (f : F →ₗ[ZMod 2] ZMod 2) (sites : Finset J)
    (label : TaggedThreeCopyRegisterLabel F J) : Complex :=
  PauliSymplectic.binaryPhaseScalar (f (taggedCubicPhaseExponent sites label))

private theorem binaryPhaseScalar_mul_self (p : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar p * PauliSymplectic.binaryPhaseScalar p = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hp : p + p = 0 := by fin_cases p <;> decide
  rw [hp, PauliSymplectic.binaryPhaseScalar_zero]

/-- The actual sign-diagonal unitary, with its own inverse supplied explicitly. -/
def taggedCubicPhaseTransport (f : F →ₗ[ZMod 2] ZMod 2) (sites : Finset J) :
    UnitaryTransport (TaggedThreeCopyRegister F J) (TaggedThreeCopyRegister F J) where
  toLinearEquiv := KT19PrimeQuditCSS.diagonalLinearEquiv
    (taggedCubicPhaseAmplitude f sites) (taggedCubicPhaseAmplitude f sites)
    (fun _ => binaryPhaseScalar_mul_self _) (fun _ => binaryPhaseScalar_mul_self _)
  map_inner := KT19PrimeQuditCSS.diagonalOperator_map_inner _ (fun label => by
    change PauliSymplectic.binaryPhaseScalar _ *
      star (PauliSymplectic.binaryPhaseScalar _) = 1
    rw [PauliSymplectic.binaryPhaseScalar_star]
    exact binaryPhaseScalar_mul_self _)

@[simp]
theorem taggedCubicPhaseTransport_apply (f : F →ₗ[ZMod 2] ZMod 2) (sites : Finset J)
    (psi : TaggedThreeCopyRegister F J) (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhaseTransport f sites psi label =
      taggedCubicPhaseAmplitude f sites label * psi label := rfl

theorem taggedCubicPhaseTransport_apply_basis (f : F →ₗ[ZMod 2] ZMod 2)
    (sites : Finset J) (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhaseTransport f sites (registerBasisKet label) =
      taggedCubicPhaseAmplitude f sites label • registerBasisKet label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [taggedCubicPhaseTransport_apply, registerBasisKet, EuclideanSpace.basisFun_apply]
  · simp [taggedCubicPhaseTransport_apply, registerBasisKet, EuclideanSpace.basisFun_apply,
      htarget]

omit [Fintype F] [Fintype J] [DecidableEq J] in
/-- A single-site factor depends on exactly the three named coordinates. -/
theorem taggedCubicPhaseAmplitude_singleton (f : F →ₗ[ZMod 2] ZMod 2) (site : J)
    (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhaseAmplitude f {site} label =
      PauliSymplectic.binaryPhaseScalar
        (f (label (.first, site) * label (.second, site) * label (.third, site))) := by
  simp [taggedCubicPhaseAmplitude, taggedCubicPhaseExponent]

/-- The local gate's amplitude is unchanged when its declared triple is unchanged. -/
theorem taggedCubicPhaseAmplitude_eq_of_agree_on_support
    (f : F →ₗ[ZMod 2] ZMod 2) (site : J)
    (x y : TaggedThreeCopyRegisterLabel F J)
    (h : ∀ coordinate ∈ coordinateSupport site, x coordinate = y coordinate) :
    taggedCubicPhaseAmplitude f {site} x = taggedCubicPhaseAmplitude f {site} y := by
  rw [taggedCubicPhaseAmplitude_singleton, taggedCubicPhaseAmplitude_singleton,
    h (.first, site) (taggedCoordinate_mem_coordinateSupport .first site),
    h (.second, site) (taggedCoordinate_mem_coordinateSupport .second site),
    h (.third, site) (taggedCoordinate_mem_coordinateSupport .third site)]

omit [Fintype F] [Fintype J] [DecidableEq J] in
/-- Binary linearity converts the total phase into the physical local product. -/
theorem taggedCubicPhaseAmplitude_eq_prod (f : F →ₗ[ZMod 2] ZMod 2)
    (sites : Finset J) (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhaseAmplitude f sites label =
      ∏ site ∈ sites, taggedCubicPhaseAmplitude f {site} label := by
  simp only [taggedCubicPhaseAmplitude, taggedCubicPhaseExponent,
    Finset.sum_singleton, map_sum, PauliSymplectic.binaryPhaseScalar_sum]

/-- The coordinatewise physical operation is a literal composition of local gates. -/
def taggedCubicPhysicalTransport (f : F →ₗ[ZMod 2] ZMod 2) :
    UnitaryTransport (TaggedThreeCopyRegister F J) (TaggedThreeCopyRegister F J) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card J) =>
    taggedCubicPhaseTransport f {taggedCczSiteEquivFin J j}

private theorem composeCubicPhases_apply (f : F →ₗ[ZMod 2] ZMod 2)
    (sites : List J) (psi : TaggedThreeCopyRegister F J)
    (label : TaggedThreeCopyRegisterLabel F J) :
    UnitaryTransport.composeList
        (sites.map fun site => taggedCubicPhaseTransport f {site}) psi label =
      (sites.map fun site => taggedCubicPhaseAmplitude f {site} label).prod * psi label := by
  induction sites generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons site sites ih =>
      change UnitaryTransport.composeList
        (sites.map fun j => taggedCubicPhaseTransport f {j})
        (taggedCubicPhaseTransport f {site} psi) label = _
      rw [ih]
      simp only [taggedCubicPhaseTransport_apply, List.map_cons, List.prod_cons]
      ring

/-- The physical product has the total source phase on every amplitude. -/
theorem taggedCubicPhysicalTransport_apply (f : F →ₗ[ZMod 2] ZMod 2)
    (psi : TaggedThreeCopyRegister F J) (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhysicalTransport f psi label =
      taggedCubicPhaseAmplitude f Finset.univ label * psi label := by
  unfold taggedCubicPhysicalTransport UnitaryTransport.composeFamily
  have hlist :
      List.ofFn (fun j : Fin (Fintype.card J) =>
        taggedCubicPhaseTransport f {taggedCczSiteEquivFin J j}) =
      (List.ofFn (taggedCczSiteEquivFin J)).map
        (fun site => taggedCubicPhaseTransport f {site}) := by
    rw [List.map_ofFn]
    rfl
  rw [hlist, composeCubicPhases_apply, List.map_ofFn, Fin.prod_ofFn]
  congr 1
  rw [taggedCubicPhaseAmplitude_eq_prod]
  exact Fintype.prod_equiv (taggedCczSiteEquivFin J) _ _ (fun _ => rfl)

theorem taggedCubicPhysicalTransport_apply_basis (f : F →ₗ[ZMod 2] ZMod 2)
    (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhysicalTransport f (registerBasisKet label) =
      taggedCubicPhaseAmplitude f Finset.univ label • registerBasisKet label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [taggedCubicPhysicalTransport_apply, registerBasisKet, EuclideanSpace.basisFun_apply]
  · simp [taggedCubicPhysicalTransport_apply, registerBasisKet, EuclideanSpace.basisFun_apply,
      htarget]

/-- Only the specified local cubic gate is allowed on each actual tagged triple. -/
inductive TaggedCubicLocalGate : Finset (TaggedThreeCopyCoordinate J) → Type u
  | at (site : J) : TaggedCubicLocalGate (coordinateSupport site)

def taggedCubicPhysicalGateModel (f : F →ₗ[ZMod 2] ZMod 2) :
    FinitePhysicalGateModel (TaggedThreeCopyCoordinate J) (TaggedThreeCopyRegister F J) where
  LocalGate := TaggedCubicLocalGate
  realize gate := match gate with
    | .at site => taggedCubicPhaseTransport f {site}

/-- The physical implementation factors over the pairwise-disjoint three-tag supports. -/
def taggedCubicPhysicalFactorization (f : F →ₗ[ZMod 2] ZMod 2) :
    PhysicalGateFactorization (taggedCubicPhysicalGateModel (J := J) f)
      (taggedCubicPhysicalTransport f) where
  factorCount := Fintype.card J
  support j := coordinateSupport (taggedCczSiteEquivFin J j)
  factor j := .at (taggedCczSiteEquivFin J j)
  pairwise_disjoint := by
    intro i j hij
    exact coordinateSupport_disjoint ((taggedCczSiteEquivFin J).injective.ne hij)
  realizes := rfl

section Encoding

variable [Fintype I] [Fintype Logical] [CharP F 2]

local instance : DecidableEq Logical := Classical.decEq _

/-- Apply the chosen functional to the already-proved field-valued cubic identity. -/
theorem taggedCubicPhaseAmplitude_coset (data : SourceInput F I Logical)
    (f : F →ₗ[ZMod 2] ZMod 2) (label : TaggedThreeCopyRegisterLabel F Logical)
    (h : ThreeCopyTag → data.H0) :
    taggedCubicPhaseAmplitude f Finset.univ (taggedShortenedCosetLabel data label h) =
      taggedCubicPhaseAmplitude f Finset.univ label := by
  unfold taggedCubicPhaseAmplitude
  congr 2
  exact taggedShortenedCosetLabel_cubic_identity data label h

/-- Every summand of the actual normalized coset encoder has the same logical phase. -/
theorem taggedCubicPhysicalTransport_apply_coset (data : SourceInput F I Logical)
    (f : F →ₗ[ZMod 2] ZMod 2) (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedCubicPhysicalTransport f (taggedShortenedCosetKet data label) =
      taggedCubicPhaseAmplitude f Finset.univ label • taggedShortenedCosetKet data label := by
  unfold taggedShortenedCosetKet
  rw [map_smul, map_sum]
  simp_rw [taggedCubicPhysicalTransport_apply_basis, taggedCubicPhaseAmplitude_coset]
  rw [← Finset.smul_sum, smul_comm]

/-- All-state intertwining for the source's arbitrary binary-linear cubic phase. -/
theorem taggedCubicPhysicalTransport_implements_logical (data : SourceInput F I Logical)
    (f : F →ₗ[ZMod 2] ZMod 2) :
    (taggedEncodedCode data).ImplementsLogicalGate
      (taggedCubicPhysicalTransport f)
      (taggedCubicPhaseTransport f Finset.univ) := by
  intro psi
  change taggedCubicPhysicalTransport f (taggedEncodingLinearMap data psi) =
    taggedEncodingLinearMap data (taggedCubicPhaseTransport f Finset.univ psi)
  change taggedCubicPhysicalTransport f
      (∑ label : TaggedThreeCopyRegisterLabel F Logical,
        psi label • taggedShortenedCosetKet data label) = _
  rw [map_sum]
  simp_rw [map_smul, taggedCubicPhysicalTransport_apply_coset]
  change (∑ label : TaggedThreeCopyRegisterLabel F Logical,
      psi label • (taggedCubicPhaseAmplitude f Finset.univ label •
        taggedShortenedCosetKet data label)) =
    ∑ label : TaggedThreeCopyRegisterLabel F Logical,
      (taggedCubicPhaseTransport f Finset.univ psi) label • taggedShortenedCosetKet data label
  apply Finset.sum_congr rfl
  intro label _
  rw [taggedCubicPhaseTransport_apply, smul_smul, mul_comm]

end Encoding

end QEC.Distillation.Ngu24MultiplicativeCCZ
