import QEC.Coding.FourDimensionalToricCode.Cellulation
import QEC.Coding.Stabilizer.LocalHamiltonian
import QEC.Coding.QLDPC.SourceValidity
/-!
# The four-dimensional toric-code Hamiltonian

This module realizes the standard periodic 4D toric CSS Hamiltonian from the
M3 chain-complex/CSS bridge.  Qubits are plaquettes, X checks are indexed by
links, and Z checks are indexed by cubes.  For lattice side length greater
than one, every selected check has exactly six plaquettes and every plaquette
participates in at most eight selected checks.

No logical-sector or energy-barrier conclusion is asserted here.
-/

noncomputable section

namespace QEC.Coding.PeriodicCubical4

open scoped Classical

def unshift {L : Nat} (x : Coord L) (a : Axis) : Coord L :=
  x - Pi.single a 1

theorem unshift_ne_self {L : Nat} [NeZero L] [Fact (1 < L)]
    (x : Coord L) (a : Axis) :
    unshift x a ≠ x := by
  intro h
  have ha := congrFun h a
  simp [unshift] at ha

theorem shift_ne_self {L : Nat} [NeZero L] [Fact (1 < L)]
    (x : Coord L) (a : Axis) :
    shift x a ≠ x := by
  intro h
  have ha := congrFun h a
  simp [shift] at ha

theorem self_ne_unshift {L : Nat} [NeZero L] [Fact (1 < L)]
    (x : Coord L) (a : Axis) :
    x ≠ unshift x a :=
  Ne.symm (unshift_ne_self x a)

theorem self_ne_shift {L : Nat} [NeZero L] [Fact (1 < L)]
    (x : Coord L) (a : Axis) :
    x ≠ shift x a :=
  Ne.symm (shift_ne_self x a)

@[simp]
theorem shift_unshift {L : Nat} (x : Coord L) (a : Axis) :
    shift (unshift x a) a = x := by
  simp [shift, unshift]

@[simp]
theorem unshift_shift {L : Nat} (x : Coord L) (a : Axis) :
    unshift (shift x a) a = x := by
  simp [shift, unshift]

theorem shift_eq_iff_eq_unshift {L : Nat} (x y : Coord L) (a : Axis) :
    shift x a = y ↔ x = unshift y a := by
  constructor
  · intro h
    rw [← h, unshift_shift]
  · intro h
    rw [h, shift_unshift]

theorem eq_shift_iff_eq_unshift {L : Nat} (x y : Coord L) (a : Axis) :
    x = shift y a ↔ y = unshift x a := by
  rw [eq_comm, shift_eq_iff_eq_unshift]

def linkPlaquettes {L : Nat} [NeZero L] (e : Link L) : Finset (Plaquette L) :=
  match e.2 with
  | .x =>
      {(e.1, .xy), (unshift e.1 .y, .xy),
       (e.1, .xz), (unshift e.1 .z, .xz),
       (e.1, .xw), (unshift e.1 .w, .xw)}
  | .y =>
      {(e.1, .xy), (unshift e.1 .x, .xy),
       (e.1, .yz), (unshift e.1 .z, .yz),
       (e.1, .yw), (unshift e.1 .w, .yw)}
  | .z =>
      {(e.1, .xz), (unshift e.1 .x, .xz),
       (e.1, .yz), (unshift e.1 .y, .yz),
       (e.1, .zw), (unshift e.1 .w, .zw)}
  | .w =>
      {(e.1, .xw), (unshift e.1 .x, .xw),
       (e.1, .yw), (unshift e.1 .y, .yw),
       (e.1, .zw), (unshift e.1 .z, .zw)}

def cubePlaquettes {L : Nat} [NeZero L] (c : Cube L) : Finset (Plaquette L) :=
  match c.2 with
  | .xyz =>
      {(c.1, .xy), (shift c.1 .z, .xy),
       (c.1, .xz), (shift c.1 .y, .xz),
       (c.1, .yz), (shift c.1 .x, .yz)}
  | .xyw =>
      {(c.1, .xy), (shift c.1 .w, .xy),
       (c.1, .xw), (shift c.1 .y, .xw),
       (c.1, .yw), (shift c.1 .x, .yw)}
  | .xzw =>
      {(c.1, .xz), (shift c.1 .w, .xz),
       (c.1, .xw), (shift c.1 .z, .xw),
       (c.1, .zw), (shift c.1 .x, .zw)}
  | .yzw =>
      {(c.1, .yz), (shift c.1 .w, .yz),
       (c.1, .yw), (shift c.1 .z, .yw),
       (c.1, .zw), (shift c.1 .y, .zw)}

theorem card_linkPlaquettes {L : Nat} [NeZero L] [Fact (1 < L)]
    (e : Link L) :
    (linkPlaquettes e).card = 6 := by
  rcases e with ⟨x, a⟩
  cases a <;> simp [linkPlaquettes, self_ne_unshift]

theorem card_cubePlaquettes {L : Nat} [NeZero L] [Fact (1 < L)]
    (c : Cube L) :
    (cubePlaquettes c).card = 6 := by
  rcases c with ⟨x, v⟩
  cases v <;> simp [cubePlaquettes, self_ne_shift]

theorem transpose_boundary2_single_apply {L : Nat} [NeZero L]
    (e : Link L) (p : Plaquette L) :
    wordLinearMapTranspose boundary2 (Pi.single e (1 : ZMod 2)) p =
      plaquetteBoundary p e := by
  classical
  simp [wordLinearMapTranspose, boundary2, linearize]
  rw [Finset.sum_eq_single e]
  · simp only [Pi.single_eq_same, one_mul]
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hbp
      simp [hbp]
    · simp
  · intro b _ hbe
    simp [hbe]
  · simp

theorem hammingSupport_transpose_boundary2_single
    {L : Nat} [NeZero L] [Fact (1 < L)] (e : Link L) :
    hammingSupport
        (wordLinearMapTranspose boundary2 (Pi.single e (1 : ZMod 2))) =
      linkPlaquettes e := by
  rcases e with ⟨x, a⟩
  ext p 
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [transpose_boundary2_single_apply]
  rcases p with ⟨y, q⟩
  cases a <;> cases q <;>
    simp [plaquetteBoundary, cellWord, linkPlaquettes] <;>
    simp only [Pi.single_apply] <;>
    split_ifs <;>
    simp_all [self_ne_shift, eq_shift_iff_eq_unshift, eq_comm]

theorem hammingSupport_cubeBoundary
    {L : Nat} [NeZero L] [Fact (1 < L)] (c : Cube L) :
    hammingSupport (cubeBoundary c) = cubePlaquettes c := by
  rcases c with ⟨x, v⟩
  ext p
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases p with ⟨y, q⟩
  cases v <;> cases q <;>
    simp [cubeBoundary, cellWord, cubePlaquettes] <;>
    simp only [Pi.single_apply] <;>
    split_ifs <;>
    simp_all [self_ne_shift, shift_ne_self]

def plaquetteLinks {L : Nat} [NeZero L] (p : Plaquette L) : Finset (Link L) :=
  match p.2 with
  | .xy =>
      {(p.1, .x), (shift p.1 .y, .x), (p.1, .y), (shift p.1 .x, .y)}
  | .xz =>
      {(p.1, .x), (shift p.1 .z, .x), (p.1, .z), (shift p.1 .x, .z)}
  | .xw =>
      {(p.1, .x), (shift p.1 .w, .x), (p.1, .w), (shift p.1 .x, .w)}
  | .yz =>
      {(p.1, .y), (shift p.1 .z, .y), (p.1, .z), (shift p.1 .y, .z)}
  | .yw =>
      {(p.1, .y), (shift p.1 .w, .y), (p.1, .w), (shift p.1 .y, .w)}
  | .zw =>
      {(p.1, .z), (shift p.1 .w, .z), (p.1, .w), (shift p.1 .z, .w)}

def plaquetteCubes {L : Nat} [NeZero L] (p : Plaquette L) : Finset (Cube L) :=
  match p.2 with
  | .xy =>
      {(p.1, .xyz), (unshift p.1 .z, .xyz),
       (p.1, .xyw), (unshift p.1 .w, .xyw)}
  | .xz =>
      {(p.1, .xyz), (unshift p.1 .y, .xyz),
       (p.1, .xzw), (unshift p.1 .w, .xzw)}
  | .xw =>
      {(p.1, .xyw), (unshift p.1 .y, .xyw),
       (p.1, .xzw), (unshift p.1 .z, .xzw)}
  | .yz =>
      {(p.1, .xyz), (unshift p.1 .x, .xyz),
       (p.1, .yzw), (unshift p.1 .w, .yzw)}
  | .yw =>
      {(p.1, .xyw), (unshift p.1 .x, .xyw),
       (p.1, .yzw), (unshift p.1 .z, .yzw)}
  | .zw =>
      {(p.1, .xzw), (unshift p.1 .x, .xzw),
       (p.1, .yzw), (unshift p.1 .y, .yzw)}

theorem mem_linkPlaquettes_iff_mem_plaquetteLinks
    {L : Nat} [NeZero L] (e : Link L) (p : Plaquette L) :
    p ∈ linkPlaquettes e ↔ e ∈ plaquetteLinks p := by
  rcases e with ⟨x, a⟩
  rcases p with ⟨y, q⟩
  cases a <;> cases q <;>
    simp [linkPlaquettes, plaquetteLinks, eq_shift_iff_eq_unshift, eq_comm]

theorem mem_cubePlaquettes_iff_mem_plaquetteCubes
    {L : Nat} [NeZero L] (c : Cube L) (p : Plaquette L) :
    p ∈ cubePlaquettes c ↔ c ∈ plaquetteCubes p := by
  rcases c with ⟨x, v⟩
  rcases p with ⟨y, q⟩
  cases v <;> cases q <;>
    simp [cubePlaquettes, plaquetteCubes, eq_shift_iff_eq_unshift, eq_comm]

theorem card_insert_four_le {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  calc
    ({a, b, c, d} : Finset α).card ≤ ({b, c, d} : Finset α).card + 1 :=
      Finset.card_insert_le ..
    _ ≤ (({c, d} : Finset α).card + 1) + 1 := by
      exact Nat.add_le_add_right (Finset.card_insert_le b {c, d}) 1
    _ ≤ ((({d} : Finset α).card + 1) + 1) + 1 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (Finset.card_insert_le c {d}) 1) 1
    _ = 4 := by simp

theorem card_plaquetteLinks_le_four {L : Nat} [NeZero L] (p : Plaquette L) :
    (plaquetteLinks p).card ≤ 4 := by
  rcases p with ⟨x, q⟩
  cases q <;> exact card_insert_four_le _ _ _ _

theorem card_plaquetteCubes_le_four {L : Nat} [NeZero L] (p : Plaquette L) :
    (plaquetteCubes p).card ≤ 4 := by
  rcases p with ⟨x, q⟩
  cases q <;> exact card_insert_four_le _ _ _ _

end QEC.Coding.PeriodicCubical4

namespace QEC.Coding.PeriodicCubical4

open scoped Classical
open PauliSymplectic

section ToricHamiltonian

variable {L : Nat} [NeZero L] [Fact (1 < L)]

/-- The standard link-X and cube-Z checks of the periodic 4D toric code. -/
noncomputable def toricGenerator :
    Sum (Link L) (Cube L) → PauliSymplectic.Binary (Plaquette L) :=
  QLDPC.chainComplexCSSRowCheck plaquetteChainComplex

/-- The source-valid stabilizer code supplied by the M3 chain-complex/CSS bridge. -/
noncomputable def toricSourceValidCode :
    StabilizerCode.SourceValidBinary (Plaquette L) :=
  plaquetteChainComplex.binaryCSSSourceValidStabilizer

omit [Fact (1 < L)] in
@[simp]
theorem toricGenerator_inl (e : Link L) :
    toricGenerator (L := L) (Sum.inl e) =
      cssXCheck
        (wordLinearMapTranspose boundary2 (Pi.single e (1 : ZMod 2))) :=
  by
    simp [toricGenerator, QLDPC.chainComplexCSSRowCheck, plaquetteChainComplex]
    congr 1
    ext q
    by_cases h : q = e <;> simp [canonicalBasisWord, Pi.single_apply, h]

omit [Fact (1 < L)] in
@[simp]
theorem toricGenerator_inr (c : Cube L) :
    toricGenerator (L := L) (Sum.inr c) =
      cssZCheck (boundary3 (Pi.single c (1 : ZMod 2))) :=
  by
    simp [toricGenerator, QLDPC.chainComplexCSSRowCheck, plaquetteChainComplex]
    congr 1
    ext q
    by_cases h : q = c <;> simp [canonicalBasisWord, Pi.single_apply, h]

@[simp]
theorem toricGenerator_support_inl (e : Link L) :
    support (toricGenerator (Sum.inl e)) = linkPlaquettes e := by
  rw [toricGenerator_inl, support_cssXCheck,
    hammingSupport_transpose_boundary2_single]

@[simp]
theorem toricGenerator_support_inr (c : Cube L) :
    support (toricGenerator (Sum.inr c)) = cubePlaquettes c := by
  rw [toricGenerator_inr, support_cssZCheck]
  simpa [boundary3] using hammingSupport_cubeBoundary c

@[simp]
theorem toricGenerator_weight (j : Sum (Link L) (Cube L)) :
    weight (toricGenerator j) = 6 := by
  cases j with
  | inl e =>
      rw [weight, toricGenerator_support_inl, card_linkPlaquettes]
  | inr c =>
      rw [weight, toricGenerator_support_inr, card_cubePlaquettes]

omit [Fact (1 < L)] in
theorem toricGenerator_self_adjoint (j : Sum (Link L) (Cube L)) :
    LinearMap.adjoint (toQubitOperator (toricGenerator j)) =
      toQubitOperator (toricGenerator j) := by
  rw [adjoint_toQubitOperator_eq_binaryDagger]
  cases j <;> simp [toricGenerator, QLDPC.chainComplexCSSRowCheck]

omit [Fact (1 < L)] in
theorem toricGenerator_generated_eq :
    generatedStabilizerSet (toricGenerator (L := L)) =
      (toricSourceValidCode (L := L)).1.generatedGroup := by
  classical
  let K := plaquetteChainComplex (L := L)
  let rows := QLDPC.chainComplexCSSRowChecks K
  have hrows := QLDPC.chainComplexCSSRowChecks_generate_stabilizerGroup K
  rw [QLDPC.FinsetGenerates] at hrows
  rw [toricSourceValidCode, ChainComplexData.binaryCSSSourceValidStabilizer]
  change generatedStabilizerSet (toricGenerator (L := L)) =
    K.binaryCSSCode.stabilizer.generatedGroup
  rw [← hrows]
  ext P
  constructor
  · intro hP
    exact QLDPC.generatedStabilizer_of_generators_generated
      (source := toricGenerator (L := L))
      (target := fun g : {Q : PauliSymplectic.Binary (Plaquette L) // Q ∈ rows} => g.1)
      (fun j => by
        let g : {Q : PauliSymplectic.Binary (Plaquette L) // Q ∈ rows} :=
          ⟨toricGenerator (L := L) j,
            (QLDPC.mem_chainComplexCSSRowChecks K
              (toricGenerator (L := L) j)).2 ⟨j, by
                simp [toricGenerator, K]⟩⟩
        exact GeneratedStabilizer.generator g)
      hP
  · intro hP
    exact QLDPC.generatedStabilizer_of_generators_generated
      (source := fun g : {Q : PauliSymplectic.Binary (Plaquette L) // Q ∈ rows} => g.1)
      (target := toricGenerator (L := L))
      (fun g => by
        rcases (QLDPC.mem_chainComplexCSSRowChecks K g.1).1 g.2 with ⟨j, hj⟩
        have ht : toricGenerator (L := L) j = g.1 := by
          simpa [toricGenerator, K] using hj
        change GeneratedStabilizer (toricGenerator (L := L)) g.1
        rw [← ht]
        exact GeneratedStabilizer.generator j)
      hP

/-- Two plaquettes are locally related when one selected link or cube check contains both. -/
def ShareSelectedCheck (p q : Plaquette L) : Prop :=
  (∃ e : Link L, p ∈ linkPlaquettes e ∧ q ∈ linkPlaquettes e) ∨
    ∃ c : Cube L, p ∈ cubePlaquettes c ∧ q ∈ cubePlaquettes c

omit [Fact (1 < L)] in
theorem ShareSelectedCheck.symm {p q : Plaquette L}
    (h : ShareSelectedCheck p q) : ShareSelectedCheck q p := by
  rcases h with ⟨e, hp, hq⟩ | ⟨c, hp, hq⟩
  · exact Or.inl ⟨e, hq, hp⟩
  · exact Or.inr ⟨c, hq, hp⟩

/--
The plaquette incidence geometry: distinct plaquettes sharing a selected
cellular check have distance one, while all other distinct pairs have distance two.
-/
noncomputable def plaquetteIncidenceGeometry :
    Locality.LatticeGeometry (Plaquette L) where
  distance p q := if p = q then 0 else if ShareSelectedCheck p q then 1 else 2
  distance_self p := by simp
  distance_symm p q := by
    by_cases hpq : p = q
    · subst q
      simp
    · have hqp : q ≠ p := Ne.symm hpq
      by_cases hshare : ShareSelectedCheck p q
      · have hshare' : ShareSelectedCheck q p := hshare.symm
        simp [hpq, hqp, hshare, hshare']
      · have hshare' : ¬ ShareSelectedCheck q p := by
          intro h
          exact hshare h.symm
        simp [hpq, hqp, hshare, hshare']

theorem toricGenerator_boundedDiameter
    (j : Sum (Link L) (Cube L)) :
    Locality.BoundedDiameter plaquetteIncidenceGeometry
      (support (toricGenerator (L := L) j) : Set (Plaquette L)) 1 := by
  intro p hp q hq
  cases j with
  | inl e =>
      have hp' : p ∈ linkPlaquettes e := by
        rw [toricGenerator_support_inl] at hp
        exact hp
      have hq' : q ∈ linkPlaquettes e := by
        rw [toricGenerator_support_inl] at hq
        exact hq
      have hshare : ShareSelectedCheck p q := Or.inl ⟨e, hp', hq'⟩
      by_cases h : p = q <;>
        simp [plaquetteIncidenceGeometry, hshare, h]
  | inr c =>
      have hp' : p ∈ cubePlaquettes c := by
        rw [toricGenerator_support_inr] at hp
        exact hp
      have hq' : q ∈ cubePlaquettes c := by
        rw [toricGenerator_support_inr] at hq
        exact hq
      have hshare : ShareSelectedCheck p q := Or.inr ⟨c, hp', hq'⟩
      by_cases h : p = q <;>
        simp [plaquetteIncidenceGeometry, hshare, h]

/-- The at most four incident link checks and at most four incident cube checks. -/
noncomputable def plaquetteIncidentChecks (p : Plaquette L) :
    Finset (Sum (Link L) (Cube L)) :=
  (plaquetteLinks p).image Sum.inl ∪ (plaquetteCubes p).image Sum.inr

omit [Fact (1 < L)] in
theorem card_plaquetteIncidentChecks_le_eight (p : Plaquette L) :
    (plaquetteIncidentChecks p).card ≤ 8 := by
  change
    ((plaquetteLinks p).image Sum.inl ∪
      (plaquetteCubes p).image Sum.inr).card ≤ 8
  calc
    ((plaquetteLinks p).image Sum.inl ∪
        (plaquetteCubes p).image Sum.inr).card ≤
        ((plaquetteLinks p).image Sum.inl).card +
          ((plaquetteCubes p).image Sum.inr).card :=
      Finset.card_union_le ..
    _ ≤ (plaquetteLinks p).card + (plaquetteCubes p).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ 4 + 4 :=
      Nat.add_le_add (card_plaquetteLinks_le_four p)
        (card_plaquetteCubes_le_four p)
    _ = 8 := rfl

theorem toricGenerator_participation_le (p : Plaquette L) :
    (Finset.univ.filter fun j : Sum (Link L) (Cube L) =>
      p ∈ support (toricGenerator (L := L) j)).card ≤ 8 := by
  apply le_trans (Finset.card_le_card (t := plaquetteIncidentChecks p) ?_)
    (card_plaquetteIncidentChecks_le_eight p)
  intro j hj
  have hp := (Finset.mem_filter.1 hj).2
  cases j with
  | inl e =>
      have hpe : p ∈ linkPlaquettes e := by
        rw [toricGenerator_support_inl] at hp
        exact hp
      have hep : e ∈ plaquetteLinks p :=
        (mem_linkPlaquettes_iff_mem_plaquetteLinks e p).1 hpe
      simp [plaquetteIncidentChecks, hep]
  | inr c =>
      have hpc : p ∈ cubePlaquettes c := by
        rw [toricGenerator_support_inr] at hp
        exact hp
      have hcp : c ∈ plaquetteCubes p :=
        (mem_cubePlaquettes_iff_mem_plaquetteCubes c p).1 hpc
      simp [plaquetteIncidentChecks, hcp]

/--
The standard unit-coefficient 4D toric-code Hamiltonian, using the exact
source-valid M3 CSS code and the full (possibly redundant) cellular check family.
-/
noncomputable def toricHamiltonian :
    StabilizerCode.LocalStabilizerHamiltonian
      (ι := Plaquette L) (κ := Sum (Link L) (Cube L)) where
  code := toricSourceValidCode
  generators := toricGenerator
  generated_eq := toricGenerator_generated_eq
  generator_self_adjoint := toricGenerator_self_adjoint
  geometry := plaquetteIncidenceGeometry
  interactionRange := 1
  interactionRange_positive := by omega
  local_support := toricGenerator_boundedDiameter
  participationBound := 8
  participationBound_positive := by omega
  participation_le := toricGenerator_participation_le

@[simp]
theorem toricHamiltonian_code :
    (toricHamiltonian (L := L)).code = toricSourceValidCode :=
  rfl

@[simp]
theorem toricHamiltonian_generators :
    (toricHamiltonian (L := L)).generators = toricGenerator :=
  rfl

theorem toricHamiltonian_generators_commute
    (j k : Sum (Link L) (Cube L)) :
    Commutes ((toricHamiltonian (L := L)).generators j)
      ((toricHamiltonian (L := L)).generators k) :=
  (toricHamiltonian (L := L)).generators_commute j k

@[simp]
theorem toricHamiltonian_term (j : Sum (Link L) (Cube L)) :
    (toricHamiltonian (L := L)).term j =
      -toQubitOperator (toricGenerator j) :=
  rfl

end ToricHamiltonian

end QEC.Coding.PeriodicCubical4
