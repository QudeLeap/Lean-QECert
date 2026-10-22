import QEC.Semantics.Dynamics.Davies.FrequencyLocality
import QEC.Coding.CSS.ParityChecks
import QEC.Coding.Stabilizer.HermitianPauli
import QEC.Locality.CorrectableRegions.SemanticDistanceErasure
import QEC.Locality.CorrectableRegions.CorrectableRegionClosure

/-! # Actual CSS row Hamiltonians and local Davies couplings -/

namespace QEC.Coding.CSSDaviesLocality
open Classical PauliSymplectic QEC.Semantics QEC.Locality QEC.Semantics.Davies
open scoped BigOperators
noncomputable section
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι] [Fintype κP] [Fintype κQ]

/-- Every binary Pauli is genuinely an identity extension from any containing region. -/
theorem pauli_supported (S : FiniteSubsystem ι) (E : Binary ι) (hE : support E ⊆ S.selected) :
    S.OperatorSupportedOnRegister (toQubitOperator E) := by
  let p : LocalPauliWordIndex S :=
    (fun i => E.vector.xPart i, fun i => E.vector.zPart i)
  have hx : embedSelectedWord S p.1 = E.vector.xPart := by
    funext i
    by_cases hi : i ∈ S.selected
    · simp [embedSelectedWord, p, hi]
    · simp only [embedSelectedWord, hi, ↓reduceDIte]
      symm
      by_contra hn
      exact hi (hE ((mem_support E i).2 (Or.inl ((mem_binarySupport _ i).2 hn))))
  have hz : embedSelectedWord S p.2 = E.vector.zPart := by
    funext i
    by_cases hi : i ∈ S.selected
    · simp [embedSelectedWord, p, hi]
    · simp only [embedSelectedWord, hi, ↓reduceDIte]
      symm
      by_contra hn
      exact hi (hE ((mem_support E i).2 (Or.inr ((mem_binarySupport _ i).2 hn))))
  have he : toQubitOperator E = binaryPhaseScalar E.phase • toQubitOperator (embeddedLocalPauli S p) := by
    simp [toQubitOperator, embeddedLocalPauli, xSupport, zSupport, hx, hz]
  rw [he, toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister]
  exact S.supported_smul _ (S.extendLocalToRegister_operatorSupportedOn _)

theorem hermitian_pauli_supported (S : FiniteSubsystem ι) (E : Binary ι)
    (hE : support E ⊆ S.selected) :
    S.OperatorSupportedOnRegister (toHermitianQubitOperator E) :=
  S.supported_smul _ (pauli_supported S E hE)

inductive Axis | x | y | z
  deriving DecidableEq

instance : Fintype Axis where
  elems := {.x,.y,.z}
  complete a := by cases a <;> simp

/-- A singleton binary representative; Hermitian correction below supplies the Y phase. -/
def singlePauli (q : ι) : Axis → Binary ι
  | .x => cssXCheck (Pi.single q 1)
  | .y => { phase := 0, vector := {xPart := Pi.single q 1, zPart := Pi.single q 1} }
  | .z => cssZCheck (Pi.single q 1)

def coupling (q : ι) (a : Axis) : Operator (Qubit.QubitRegister ι) :=
  toHermitianQubitOperator (singlePauli q a)

@[simp] theorem binarySupport_single (q : ι) : binarySupport (Pi.single q (1 : ZMod 2)) = {q} := by
  ext i
  simp [mem_binarySupport, Pi.single_apply]

@[simp] theorem support_singlePauli (q : ι) (a : Axis) : support (singlePauli q a) = {q} := by
  cases a <;> simp [singlePauli, cssXCheck, cssZCheck, support, xSupport, zSupport]

@[simp] theorem coupling_x (q : ι) : coupling q .x = Qubit.localX q := by
  simp [coupling, singlePauli, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, cssXCheck, xSupport, zSupport,
    toQubitOperator, Qubit.localXSupport_singleton]

@[simp] theorem coupling_z (q : ι) : coupling q .z = Qubit.localZ q := by
  simp [coupling, singlePauli, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, cssZCheck, xSupport, zSupport,
    toQubitOperator, Qubit.localZSupport_singleton]

@[simp] theorem coupling_y (q : ι) : coupling q .y = Complex.I • (Qubit.localX q * Qubit.localZ q) := by
  simp [coupling, singlePauli, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport, toQubitOperator,
    Qubit.localXSupport_singleton, Qubit.localZSupport_singleton]

theorem coupling_adjoint (q : ι) (a : Axis) : LinearMap.adjoint (coupling q a) = coupling q a :=
  adjoint_toHermitianQubitOperator_eq_self _

variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)

def row (j : Sum κP κQ) : Binary ι := binaryCSSParityCheckGenerators P Q j

def rowOperator (j : Sum κP κQ) : Operator (Qubit.QubitRegister ι) := toQubitOperator (row P Q j)
def rowSupport (j : Sum κP κQ) : Finset ι := support (row P Q j)

theorem row_hermitian (j : Sum κP κQ) : toHermitianQubitOperator (row P Q j) = rowOperator P Q j := by
  cases j <;> simp [row, rowOperator, binaryCSSParityCheckGenerators, toHermitianQubitOperator,
    hermitianPhaseScalar, binaryOverlapCount, binaryOverlapSupport, cssZCheck, cssXCheck,
    zSupport, xSupport]

theorem row_adjoint (j : Sum κP κQ) : LinearMap.adjoint (rowOperator P Q j) = rowOperator P Q j := by
  rw [← row_hermitian, adjoint_toHermitianQubitOperator_eq_self]

variable (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
include horth

theorem rows_commute (j k : Sum κP κQ) : Commute (rowOperator P Q j) (rowOperator P Q k) := by
  let C := binaryCSSStabilizerCodeOfParityChecks P Q horth
  have hm : ∀ l, row P Q l ∈ C.generatedGroup := by
    intro l
    rw [← binaryCSSParityCheckGenerators_generate_generatedGroup P Q horth]
    exact GeneratedStabilizer.generator l
  exact toQubitOperator_commute_of_commutes _ _ (C.generatedGroup_pairwise_commutes (hm j) (hm k))

omit horth in
/-- Literal selected-row Hamiltonian; identity and repeated rows are retained. -/
def hamiltonian : Operator (Qubit.QubitRegister ι) := -∑ j, rowOperator P Q j

omit horth in
theorem hamiltonian_symmetric : (hamiltonian P Q).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  simp [hamiltonian, row_adjoint]

omit horth in
def incident (q : ι) : Finset (Sum κP κQ) := Finset.univ.filter (fun j => q ∈ rowSupport P Q j)
omit horth in
def region (q : ι) : Finset ι := {q} ∪ (incident P Q q).biUnion (rowSupport P Q)
omit horth in
def subsystem (q : ι) : FiniteSubsystem ι := ⟨region P Q q⟩
omit horth in
def incidentHamiltonian (q : ι) : Operator (Qubit.QubitRegister ι) := -∑ j ∈ incident P Q q, rowOperator P Q j
omit horth in
def remainderHamiltonian (q : ι) : Operator (Qubit.QubitRegister ι) :=
  -∑ j ∈ (incident P Q q)ᶜ, rowOperator P Q j

omit horth in
theorem hamiltonian_split (q : ι) : hamiltonian P Q = incidentHamiltonian P Q q + remainderHamiltonian P Q q := by
  unfold hamiltonian incidentHamiltonian remainderHamiltonian
  rw [← neg_add, Finset.sum_add_sum_compl]

omit horth in
theorem incidentHamiltonian_symmetric (q : ι) : (incidentHamiltonian P Q q).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  simp [incidentHamiltonian, row_adjoint]

theorem incident_remainder_commute (q : ι) : Commute (incidentHamiltonian P Q q) (remainderHamiltonian P Q q) := by
  unfold incidentHamiltonian remainderHamiltonian
  apply Commute.neg_left
  apply Commute.neg_right
  apply Commute.sum_left
  intro j _
  apply Commute.sum_right
  intro k _
  exact rows_commute P Q horth j k

omit horth in
theorem remainder_coupling_commute (q : ι) (a : Axis) : Commute (remainderHamiltonian P Q q) (coupling q a) := by
  unfold remainderHamiltonian
  apply Commute.neg_left
  apply Commute.sum_left
  intro j hj
  have hn : q ∉ rowSupport P Q j := by simpa [incident] using hj
  have hd : Disjoint (support (row P Q j)) (support (singlePauli q a)) := by
    rw [support_singlePauli, Finset.disjoint_singleton_right]
    exact hn
  have hc : Commute (toQubitOperator (row P Q j)) (toQubitOperator (singlePauli q a)) :=
    toQubitOperator_commute_of_commutes _ _ (commutes_of_disjoint_support _ _ hd)
  exact hc.smul_right _

omit horth in
theorem mem_region_self (q : ι) : q ∈ region P Q q := by simp [region]
omit horth in
theorem rowSupport_subset_region (q : ι) {j : Sum κP κQ} (hj : j ∈ incident P Q q) :
    rowSupport P Q j ⊆ region P Q q := by
  intro i hi
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,hi⟩)

omit horth in
theorem incidentHamiltonian_supported (q : ι) :
    (subsystem P Q q).OperatorSupportedOnRegister (incidentHamiltonian P Q q) := by
  simpa [incidentHamiltonian] using (subsystem P Q q).supported_smul (-1)
    ((subsystem P Q q).supported_sum (incident P Q q) (rowOperator P Q)
      (fun j hj => pauli_supported _ _ (rowSupport_subset_region P Q q hj)))

omit horth in
theorem coupling_supported (q : ι) (a : Axis) :
    (subsystem P Q q).OperatorSupportedOnRegister (coupling q a) := by
  apply hermitian_pauli_supported
  rw [support_singlePauli, Finset.singleton_subset_iff]
  exact mem_region_self P Q q

/-- Equality to the true local-H component, with every equal-frequency term retained. -/
theorem frequency_eq_incident (q : ι) (a : Axis) (ω : ℝ) :
    actualFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q) (coupling q a) ω =
      actualFrequency (incidentHamiltonian P Q q) (incidentHamiltonian_symmetric P Q q) (coupling q a) ω := by
  have hs : (incidentHamiltonian P Q q + remainderHamiltonian P Q q).IsSymmetric := by
    rw [← hamiltonian_split]
    exact hamiltonian_symmetric P Q
  simpa only [← hamiltonian_split P Q q] using
    actualFrequency_add_commuting_remainder _ _ _ (incidentHamiltonian_symmetric P Q q) hs
      (incident_remainder_commute P Q horth q) (remainder_coupling_commute P Q q a) ω

theorem frequency_supported (q : ι) (a : Axis) (ω : ℝ) :
    (subsystem P Q q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q) (coupling q a) ω) := by
  rw [frequency_eq_incident P Q horth]
  exact actualFrequency_supported _ _ _ _ (incidentHamiltonian_supported P Q q) (coupling_supported P Q q a) ω

theorem weightedJump_supported
    (rate : (ι × Axis) → HamiltonianFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q) → ℝ)
    (q : ι) (a : Axis) (ω : HamiltonianFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q)) :
    (subsystem P Q q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian P Q) (hamiltonian_symmetric P Q)
        (fun qa : ι × Axis => coupling qa.1 qa.2) rate ((q,a),ω)) := by
  exact (subsystem P Q q).supported_smul _ (frequency_supported P Q horth q a ω.val)

omit horth in
theorem region_card_le (q : ι) (d w : Nat) (hd : (incident P Q q).card ≤ d)
    (hw : ∀ j, (rowSupport P Q j).card ≤ w) : (region P Q q).card ≤ 1+d*w := by
  calc
    (region P Q q).card ≤ ({q} : Finset ι).card + ((incident P Q q).biUnion (rowSupport P Q)).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + ∑ j ∈ incident P Q q, (rowSupport P Q j).card := by
      simpa using Nat.add_le_add_left (Finset.card_biUnion_le) 1
    _ ≤ 1 + (incident P Q q).card*w := by
      gcongr
      simpa using Finset.sum_le_sum (fun j (_ : j ∈ incident P Q q) => hw j)
    _ ≤ 1+d*w := by gcongr

omit horth in
theorem region_dist_center (J : ι → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ j, ∀ x ∈ rowSupport P Q j, ∀ y ∈ rowSupport P Q j, dist (J x) (J y) ≤ r)
    (q x : ι) (hx : x ∈ region P Q q) : dist (J q) (J x) ≤ r := by
  rcases Finset.mem_union.mp hx with hx | hx
  · have h : x=q := Finset.mem_singleton.mp hx
    subst x
    simpa using hr
  · obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp hx
    exact hs j q (by simpa [incident] using hj) x hx

omit horth in
theorem region_diameter (J : ι → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ j, ∀ x ∈ rowSupport P Q j, ∀ y ∈ rowSupport P Q j, dist (J x) (J y) ≤ r)
    (q x y : ι) (hx : x ∈ region P Q q) (hy : y ∈ region P Q q) : dist (J x) (J y) ≤ 2*r := by
  have h1 := region_dist_center P Q J r hr hs q x hx
  have h2 := region_dist_center P Q J r hr hs q y hy
  have ht := dist_triangle (J x) (J q) (J y)
  rw [dist_comm (J x) (J q)] at ht
  linarith

end
end QEC.Coding.CSSDaviesLocality
