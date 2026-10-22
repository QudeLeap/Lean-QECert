import QEC.Coding.FourDimensionalToricCode.EnergyBarrierLowerBound
import QEC.Coding.FourDimensionalToricCode.MembraneSweep

/-!
# Coordinate symmetries of the periodic four-dimensional toric code

This module transports the proved `xy` membrane geometry through six explicit
involutive coordinate frames.  The frame indexed by `p` sends the local `xy`
plane to `p`.  It is the symmetry layer used by the all-sector integration
theorem; it introduces no new Hamiltonian, path, or energy assumptions.
-/

noncomputable section

namespace QEC.Coding.PeriodicCubical4

open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian

/-- An involutive coordinate permutation sending the local `xy` plane to `p`. -/
def planeAxisFrame : Plane -> Axis -> Axis
  | .xy, a => a
  | .xz, .x => .x
  | .xz, .y => .z
  | .xz, .z => .y
  | .xz, .w => .w
  | .xw, .x => .x
  | .xw, .y => .w
  | .xw, .z => .z
  | .xw, .w => .y
  | .yz, .x => .z
  | .yz, .y => .y
  | .yz, .z => .x
  | .yz, .w => .w
  | .yw, .x => .w
  | .yw, .y => .y
  | .yw, .z => .z
  | .yw, .w => .x
  | .zw, .x => .z
  | .zw, .y => .w
  | .zw, .z => .x
  | .zw, .w => .y

@[simp] theorem planeAxisFrame_involutive (p : Plane) (a : Axis) :
    planeAxisFrame p (planeAxisFrame p a) = a := by
  cases p <;> cases a <;> rfl

/-- The axis permutation bundled as an equivalence. -/
def planeAxisEquiv (p : Plane) : Axis ≃ Axis where
  toFun := planeAxisFrame p
  invFun := planeAxisFrame p
  left_inv := planeAxisFrame_involutive p
  right_inv := planeAxisFrame_involutive p

/-- The induced involutive permutation of coordinate planes. -/
def planeFrame : Plane -> Plane -> Plane
  | .xy, q => q
  | .xz, .xy => .xz
  | .xz, .xz => .xy
  | .xz, .xw => .xw
  | .xz, .yz => .yz
  | .xz, .yw => .zw
  | .xz, .zw => .yw
  | .xw, .xy => .xw
  | .xw, .xz => .xz
  | .xw, .xw => .xy
  | .xw, .yz => .zw
  | .xw, .yw => .yw
  | .xw, .zw => .yz
  | .yz, .xy => .yz
  | .yz, .xz => .xz
  | .yz, .xw => .zw
  | .yz, .yz => .xy
  | .yz, .yw => .yw
  | .yz, .zw => .xw
  | .yw, .xy => .yw
  | .yw, .xz => .zw
  | .yw, .xw => .xw
  | .yw, .yz => .yz
  | .yw, .yw => .xy
  | .yw, .zw => .xz
  | .zw, .xy => .zw
  | .zw, .xz => .xz
  | .zw, .xw => .yz
  | .zw, .yz => .xw
  | .zw, .yw => .yw
  | .zw, .zw => .xy

@[simp] theorem planeFrame_xy (p : Plane) : planeFrame p .xy = p := by
  cases p <;> rfl

@[simp] theorem planeFrame_involutive (p q : Plane) :
    planeFrame p (planeFrame p q) = q := by
  cases p <;> cases q <;> rfl

/-- The plane permutation bundled as an equivalence. -/
def planeEquiv (p : Plane) : Plane ≃ Plane where
  toFun := planeFrame p
  invFun := planeFrame p
  left_inv := planeFrame_involutive p
  right_inv := planeFrame_involutive p

/-- The induced permutation of coordinate three-volumes. -/
def volumeFrame : Plane -> Volume -> Volume
  | .xy, v => v
  | .xz, .xyz => .xyz
  | .xz, .xyw => .xzw
  | .xz, .xzw => .xyw
  | .xz, .yzw => .yzw
  | .xw, .xyz => .xzw
  | .xw, .xyw => .xyw
  | .xw, .xzw => .xyz
  | .xw, .yzw => .yzw
  | .yz, .xyz => .xyz
  | .yz, .xyw => .yzw
  | .yz, .xzw => .xzw
  | .yz, .yzw => .xyw
  | .yw, .xyz => .yzw
  | .yw, .xyw => .xyw
  | .yw, .xzw => .xzw
  | .yw, .yzw => .xyz
  | .zw, .xyz => .xzw
  | .zw, .xyw => .yzw
  | .zw, .xzw => .xyz
  | .zw, .yzw => .xyw

@[simp] theorem volumeFrame_involutive (p : Plane) (v : Volume) :
    volumeFrame p (volumeFrame p v) = v := by
  cases p <;> cases v <;> rfl

/-- The volume permutation bundled as an equivalence. -/
def volumeEquiv (p : Plane) : Volume ≃ Volume where
  toFun := volumeFrame p
  invFun := volumeFrame p
  left_inv := volumeFrame_involutive p
  right_inv := volumeFrame_involutive p

/-- Reindex periodic coordinates through a selected coordinate frame. -/
def frameCoord {L : Nat} (p : Plane) (c : Coord L) : Coord L :=
  fun a => c (planeAxisFrame p a)

@[simp] theorem frameCoord_apply {L : Nat} (p : Plane) (c : Coord L) (a : Axis) :
    frameCoord p c a = c (planeAxisFrame p a) := rfl

@[simp] theorem frameCoord_involutive {L : Nat} (p : Plane) (c : Coord L) :
    frameCoord p (frameCoord p c) = c := by
  funext a
  simp [frameCoord]

/-- Coordinate reindexing bundled as an equivalence. -/
def coordEquiv {L : Nat} (p : Plane) : Coord L ≃ Coord L where
  toFun := frameCoord p
  invFun := frameCoord p
  left_inv := frameCoord_involutive p
  right_inv := frameCoord_involutive p

@[simp] theorem frameCoord_shift {L : Nat} (p : Plane) (c : Coord L) (a : Axis) :
    frameCoord p (shift c a) = shift (frameCoord p c) (planeAxisFrame p a) := by
  funext b
  cases p <;> cases a <;> cases b <;> simp [frameCoord, shift, planeAxisFrame]

/-- Relabel a link through a coordinate frame. -/
def frameLink {L : Nat} (p : Plane) (e : Link L) : Link L :=
  (frameCoord p e.1, planeAxisFrame p e.2)

/-- Relabel a plaquette through a coordinate frame. -/
def framePlaquette {L : Nat} (p : Plane) (q : Plaquette L) : Plaquette L :=
  (frameCoord p q.1, planeFrame p q.2)

/-- Relabel a cube through a coordinate frame. -/
def frameCube {L : Nat} (p : Plane) (c : Cube L) : Cube L :=
  (frameCoord p c.1, volumeFrame p c.2)

@[simp] theorem frameLink_involutive {L : Nat} (p : Plane) (e : Link L) :
    frameLink p (frameLink p e) = e := by
  rcases e with ⟨c, a⟩
  simp [frameLink]

@[simp] theorem framePlaquette_involutive {L : Nat} (p : Plane) (q : Plaquette L) :
    framePlaquette p (framePlaquette p q) = q := by
  rcases q with ⟨c, r⟩
  simp [framePlaquette]

@[simp] theorem frameCube_involutive {L : Nat} (p : Plane) (c : Cube L) :
    frameCube p (frameCube p c) = c := by
  rcases c with ⟨x, v⟩
  simp [frameCube]

def linkEquiv {L : Nat} (p : Plane) : Link L ≃ Link L where
  toFun := frameLink p
  invFun := frameLink p
  left_inv := frameLink_involutive p
  right_inv := frameLink_involutive p

def plaquetteEquiv {L : Nat} (p : Plane) : Plaquette L ≃ Plaquette L where
  toFun := framePlaquette p
  invFun := framePlaquette p
  left_inv := framePlaquette_involutive p
  right_inv := framePlaquette_involutive p

def cubeEquiv {L : Nat} (p : Plane) : Cube L ≃ Cube L where
  toFun := frameCube p
  invFun := frameCube p
  left_inv := frameCube_involutive p
  right_inv := frameCube_involutive p

/-- Reindex a finite word along an equivalence of coordinate types. -/
def wordReindex {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) : Word (ZMod 2) alpha ≃ₗ[ZMod 2] Word (ZMod 2) beta where
  toFun m b := m (e.symm b)
  invFun n a := n (e a)
  left_inv m := by funext a; simp
  right_inv n := by funext b; simp
  map_add' x y := by funext b; rfl
  map_smul' r x := by funext b; rfl

@[simp] theorem wordReindex_cellWord {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    (e : alpha ≃ beta) (a : alpha) :
    wordReindex e (cellWord a) = cellWord (e a) := by
  ext b
  simp [wordReindex, cellWord, Pi.single_apply, e.symm_apply_eq]

@[simp] theorem wordReindex_single {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    (e : alpha ≃ beta) (a : alpha) (r : ZMod 2) :
    wordReindex e (Pi.single a r) = Pi.single (e a) r := by
  ext b
  simp [wordReindex, Pi.single_apply, e.symm_apply_eq]

abbrev frameLinkWord {L : Nat} [NeZero L] (p : Plane) :=
  wordReindex (linkEquiv (L := L) p)

abbrev framePlaquetteWord {L : Nat} [NeZero L] (p : Plane) :=
  wordReindex (plaquetteEquiv (L := L) p)

abbrev frameCubeWord {L : Nat} [NeZero L] (p : Plane) :=
  wordReindex (cubeEquiv (L := L) p)

@[simp] theorem framePlaquetteWord_apply {L : Nat} [NeZero L]
    (p : Plane) (m : Word (ZMod 2) (Plaquette L)) (q : Plaquette L) :
    framePlaquetteWord p m q = m (framePlaquette p q) := by
  rfl

@[simp] theorem frameLinkWord_cellWord {L : Nat} [NeZero L]
    (p : Plane) (e : Link L) :
    frameLinkWord p (cellWord e) = cellWord (frameLink p e) := by
  exact wordReindex_cellWord (linkEquiv p) e

@[simp] theorem framePlaquetteWord_cellWord {L : Nat} [NeZero L]
    (p : Plane) (q : Plaquette L) :
    framePlaquetteWord p (cellWord q) = cellWord (framePlaquette p q) := by
  exact wordReindex_cellWord (plaquetteEquiv p) q

@[simp] theorem frameCubeWord_cellWord {L : Nat} [NeZero L]
    (p : Plane) (c : Cube L) :
    frameCubeWord p (cellWord c) = cellWord (frameCube p c) := by
  exact wordReindex_cellWord (cubeEquiv p) c

set_option maxHeartbeats 1000000

/-- Coordinate frames carry plaquette boundaries to plaquette boundaries. -/
theorem frameLinkWord_plaquetteBoundary {L : Nat} [NeZero L]
    (p : Plane) (q : Plaquette L) :
    frameLinkWord p (plaquetteBoundary q) =
      plaquetteBoundary (framePlaquette p q) := by
  rcases q with ⟨c, q⟩
  cases p <;> cases q <;>
    simp [plaquetteBoundary, linkEquiv, frameLink, framePlaquette,
      frameCoord_shift, planeAxisFrame, planeFrame] <;> abel

/-- Coordinate frames carry cube boundaries to cube boundaries. -/
theorem framePlaquetteWord_cubeBoundary {L : Nat} [NeZero L]
    (p : Plane) (c : Cube L) :
    framePlaquetteWord p (cubeBoundary c) =
      cubeBoundary (frameCube p c) := by
  rcases c with ⟨x, v⟩
  cases p <;> cases v <;>
    simp [cubeBoundary, plaquetteEquiv, framePlaquette, frameCube,
      frameCoord_shift, planeAxisFrame, planeFrame, volumeFrame] <;> abel

/-- Coordinate relabeling commutes with the plaquette-to-link boundary. -/
theorem frame_boundary2 {L : Nat} [NeZero L]
    (p : Plane) (m : Word (ZMod 2) (Plaquette L)) :
    frameLinkWord p (boundary2 m) =
      boundary2 (framePlaquetteWord p m) := by
  rw [← word_eq_sum_single (F := ZMod 2) m]
  simp only [map_sum, boundary2, linearize_single, map_smul,
    wordReindex_single, frameLinkWord_plaquetteBoundary]
  simp [plaquetteEquiv]

/-- Coordinate relabeling commutes with the cube-to-plaquette boundary. -/
theorem frame_boundary3 {L : Nat} [NeZero L]
    (p : Plane) (m : Word (ZMod 2) (Cube L)) :
    framePlaquetteWord p (boundary3 m) =
      boundary3 (frameCubeWord p m) := by
  rw [← word_eq_sum_single (F := ZMod 2) m]
  simp only [map_sum, boundary3, linearize_single, map_smul,
    wordReindex_single, framePlaquetteWord_cubeBoundary]
  simp [cubeEquiv]

/-- Reindexing both arguments by the same frame preserves the word pairing. -/
theorem wordPairing_framePlaquetteWord {L : Nat} [NeZero L]
    (p : Plane) (x y : Word (ZMod 2) (Plaquette L)) :
    wordPairing (framePlaquetteWord p x) (framePlaquetteWord p y) =
      wordPairing x y := by
  simpa [wordPairing_apply, dotProduct, framePlaquetteWord_apply,
    plaquetteEquiv] using
      (Equiv.sum_comp (plaquetteEquiv (L := L) p) (fun q => x q * y q))

/-- Moving one framed argument across the pairing frames the other one. -/
theorem wordPairing_framePlaquetteWord_left {L : Nat} [NeZero L]
    (p : Plane) (x y : Word (ZMod 2) (Plaquette L)) :
    wordPairing (framePlaquetteWord p x) y =
      wordPairing x (framePlaquetteWord p y) := by
  calc
    wordPairing (framePlaquetteWord p x) y =
        wordPairing (framePlaquetteWord p x)
          (framePlaquetteWord p (framePlaquetteWord p y)) := by
      congr 1
      exact (wordReindex (plaquetteEquiv p)).symm_apply_apply y |>.symm
    _ = wordPairing x (framePlaquetteWord p y) :=
      wordPairing_framePlaquetteWord p x (framePlaquetteWord p y)

/-- The transpose plaquette coboundary is equivariant under coordinate frames. -/
theorem frame_transpose_boundary2 {L : Nat} [NeZero L]
    (p : Plane) (e : Word (ZMod 2) (Link L)) :
    framePlaquetteWord p (wordLinearMapTranspose boundary2 e) =
      wordLinearMapTranspose boundary2 (frameLinkWord p e) := by
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate (F := ZMod 2)).left
  intro m
  have hpair :
    wordPairing (framePlaquetteWord p (wordLinearMapTranspose boundary2 e)) m =
      wordPairing (wordLinearMapTranspose boundary2 (frameLinkWord p e)) m := by
    calc
      wordPairing (framePlaquetteWord p (wordLinearMapTranspose boundary2 e)) m =
          wordPairing (wordLinearMapTranspose boundary2 e)
          (framePlaquetteWord p m) :=
        wordPairing_framePlaquetteWord_left p _ _
      _ = wordPairing e (boundary2 (framePlaquetteWord p m)) :=
        wordPairing_wordLinearMapTranspose boundary2 e (framePlaquetteWord p m)
      _ = wordPairing e (frameLinkWord p (boundary2 m)) := by
        rw [frame_boundary2]
      _ = wordPairing (frameLinkWord p e) (boundary2 m) := by
        simpa [wordPairing_apply, dotProduct, linkEquiv, wordReindex] using
          (Equiv.sum_comp (linkEquiv (L := L) p)
            (fun q => e q * boundary2 m (frameLink p q))).symm
      _ = wordPairing (wordLinearMapTranspose boundary2 (frameLinkWord p e)) m :=
        (wordPairing_wordLinearMapTranspose boundary2 (frameLinkWord p e) m).symm
  simpa [wordPairing_apply, dotProduct_sub] using sub_eq_zero.mpr hpair

/-- Relabel both X and Z coordinates of a binary Pauli. -/
def frameBinary {L : Nat} [NeZero L] (p : Plane)
    (E : Binary (Plaquette L)) : Binary (Plaquette L) :=
  { phase := E.phase
    vector :=
      { xPart := framePlaquetteWord p E.vector.xPart
        zPart := framePlaquetteWord p E.vector.zPart } }

@[simp] theorem frameBinary_phase {L : Nat} [NeZero L]
    (p : Plane) (E : Binary (Plaquette L)) :
    (frameBinary p E).phase = E.phase := rfl

@[simp] theorem frameBinary_xPart {L : Nat} [NeZero L]
    (p : Plane) (E : Binary (Plaquette L)) :
    (frameBinary p E).vector.xPart = framePlaquetteWord p E.vector.xPart := rfl

@[simp] theorem frameBinary_zPart {L : Nat} [NeZero L]
    (p : Plane) (E : Binary (Plaquette L)) :
    (frameBinary p E).vector.zPart = framePlaquetteWord p E.vector.zPart := rfl

@[simp] theorem framePlaquetteWord_involutive {L : Nat} [NeZero L]
    (p : Plane) (m : Word (ZMod 2) (Plaquette L)) :
    framePlaquetteWord p (framePlaquetteWord p m) = m := by
  ext q
  simp [framePlaquetteWord_apply]

@[simp] theorem frameBinary_involutive {L : Nat} [NeZero L]
    (p : Plane) (E : Binary (Plaquette L)) :
    frameBinary p (frameBinary p E) = E := by
  rcases E with ⟨phase, vector⟩
  rcases vector with ⟨x, z⟩
  simp [frameBinary]

@[simp] theorem frameBinary_binaryOne {L : Nat} [NeZero L] (p : Plane) :
    frameBinary p (binaryOne (ι := Plaquette L)) = binaryOne := by
  rfl

@[simp] theorem frameBinary_cssXCheck {L : Nat} [NeZero L]
    (p : Plane) (x : Word (ZMod 2) (Plaquette L)) :
    frameBinary p (cssXCheck x) = cssXCheck (framePlaquetteWord p x) := by
  rfl

@[simp] theorem frameBinary_cssZCheck {L : Nat} [NeZero L]
    (p : Plane) (z : Word (ZMod 2) (Plaquette L)) :
    frameBinary p (cssZCheck z) = cssZCheck (framePlaquetteWord p z) := by
  rfl

theorem frameBinary_binaryMul {L : Nat} [NeZero L]
    (p : Plane) (E F : Binary (Plaquette L)) :
    frameBinary p (binaryMul E F) =
      binaryMul (frameBinary p E) (frameBinary p F) := by
  rcases E with ⟨ePhase, eVector⟩
  rcases eVector with ⟨ex, ez⟩
  rcases F with ⟨fPhase, fVector⟩
  rcases fVector with ⟨fx, fz⟩
  apply (binaryEquivPhaseXPartZPart (ι := Plaquette L)).injective
  apply Prod.ext
  · change
      ePhase + fPhase + wordPairing fx ez =
        ePhase + fPhase +
          wordPairing (framePlaquetteWord p fx) (framePlaquetteWord p ez)
    rw [wordPairing_framePlaquetteWord]
  · apply Prod.ext <;>
      simp [binaryEquivPhaseXPartZPart, frameBinary, binaryMul]

@[simp] theorem mem_support_frameBinary {L : Nat} [NeZero L]
    (p : Plane) (E : Binary (Plaquette L)) (q : Plaquette L) :
    q ∈ support (frameBinary p E) ↔ framePlaquette p q ∈ support E := by
  simp [support, xSupport, zSupport, binarySupport, frameBinary,
    framePlaquetteWord_apply]

/-- Binary Pauli weight is invariant under coordinate relabeling. -/
theorem weight_frameBinary {L : Nat} [NeZero L]
    (p : Plane) (E : Binary (Plaquette L)) :
    weight (frameBinary p E) = weight E := by
  classical
  let supportEquiv :
      {q // q ∈ support (frameBinary p E)} ≃ {q // q ∈ support E} :=
    { toFun := fun q => ⟨framePlaquette p q.1, by
          exact (mem_support_frameBinary p E q.1).mp q.2⟩
      invFun := fun q => ⟨framePlaquette p q.1, by
          apply (mem_support_frameBinary p E (framePlaquette p q.1)).mpr
          simpa using q.2⟩
      left_inv := by intro q; exact Subtype.ext (framePlaquette_involutive p q.1)
      right_inv := by intro q; exact Subtype.ext (framePlaquette_involutive p q.1) }
  simpa only [weight, Fintype.card_coe] using Fintype.card_congr supportEquiv

/-- Relabel the selected link/cube generator index. -/
def frameGeneratorIndex {L : Nat} (p : Plane) :
    Sum (Link L) (Cube L) -> Sum (Link L) (Cube L)
  | .inl e => .inl (frameLink p e)
  | .inr c => .inr (frameCube p c)

@[simp] theorem frameGeneratorIndex_involutive {L : Nat}
    (p : Plane) (j : Sum (Link L) (Cube L)) :
    frameGeneratorIndex p (frameGeneratorIndex p j) = j := by
  cases j <;> simp [frameGeneratorIndex]

def generatorIndexEquiv {L : Nat} (p : Plane) :
    Sum (Link L) (Cube L) ≃ Sum (Link L) (Cube L) where
  toFun := frameGeneratorIndex p
  invFun := frameGeneratorIndex p
  left_inv := frameGeneratorIndex_involutive p
  right_inv := frameGeneratorIndex_involutive p

/-- Coordinate frames carry every selected toric generator to the relabeled one. -/
theorem frameBinary_toricGenerator {L : Nat} [NeZero L] [Fact (1 < L)]
    (p : Plane) (j : Sum (Link L) (Cube L)) :
    frameBinary p (toricGenerator (L := L) j) =
      toricGenerator (frameGeneratorIndex p j) := by
  cases j with
  | inl e =>
      rw [toricGenerator_inl, frameBinary_cssXCheck,
        frame_transpose_boundary2, wordReindex_single]
      simp [toricGenerator_inl, frameGeneratorIndex, linkEquiv]
  | inr c =>
      rw [toricGenerator_inr, frameBinary_cssZCheck,
        frame_boundary3, wordReindex_single]
      simp [toricGenerator_inr, frameGeneratorIndex, cubeEquiv]

/-- The symplectic form is invariant under simultaneous coordinate framing. -/
theorem symplecticForm_frameBinary {L : Nat} [NeZero L]
    (p : Plane) (E F : Binary (Plaquette L)) :
    symplecticForm (frameBinary p E).vector (frameBinary p F).vector =
      symplecticForm E.vector F.vector := by
  simpa [symplecticForm, frameBinary, framePlaquetteWord_apply,
    plaquetteEquiv] using
      (Equiv.sum_comp (plaquetteEquiv (L := L) p) (fun q =>
        E.vector.xPart q * F.vector.zPart q -
          E.vector.zPart q * F.vector.xPart q))

@[simp] theorem commutes_frameBinary_iff {L : Nat} [NeZero L]
    (p : Plane) (E F : Binary (Plaquette L)) :
    Commutes (frameBinary p E) (frameBinary p F) ↔ Commutes E F := by
  change
    symplecticForm (frameBinary p E).vector (frameBinary p F).vector = 0 ↔
      symplecticForm E.vector F.vector = 0
  rw [symplecticForm_frameBinary]

/-- Membership in the violated-generator set is transported by the generator frame. -/
theorem mem_violatedGenerators_frameBinary_iff {L : Nat}
    [NeZero L] [Fact (1 < L)]
    (p : Plane) (E : Binary (Plaquette L))
    (j : Sum (Link L) (Cube L)) :
    j ∈ (toricHamiltonian (L := L)).violatedGenerators (frameBinary p E) ↔
      frameGeneratorIndex p j ∈
        (toricHamiltonian (L := L)).violatedGenerators E := by
  simp only [mem_violatedGenerators, toricHamiltonian_generators]
  have hgenerator :
      frameBinary p (toricGenerator (frameGeneratorIndex p j)) =
        toricGenerator j := by
    simpa using frameBinary_toricGenerator p (frameGeneratorIndex p j)
  rw [← hgenerator]
  exact not_congr (commutes_frameBinary_iff p E
    (toricGenerator (frameGeneratorIndex p j)))

/-- BT excess energy is invariant under coordinate framing. -/
theorem btExcessEnergy_frameBinary {L : Nat} [NeZero L] [Fact (1 < L)]
    (p : Plane) (E : Binary (Plaquette L)) :
    (toricHamiltonian (L := L)).btExcessEnergy (frameBinary p E) =
      (toricHamiltonian (L := L)).btExcessEnergy E := by
  classical
  let violatedEquiv :
      {j // j ∈ (toricHamiltonian (L := L)).violatedGenerators (frameBinary p E)} ≃
        {j // j ∈ (toricHamiltonian (L := L)).violatedGenerators E} :=
    { toFun := fun j => ⟨frameGeneratorIndex p j.1,
          (mem_violatedGenerators_frameBinary_iff p E j.1).mp j.2⟩
      invFun := fun j => ⟨frameGeneratorIndex p j.1, by
          apply (mem_violatedGenerators_frameBinary_iff p E
            (frameGeneratorIndex p j.1)).mpr
          simpa using j.2⟩
      left_inv := by
        intro j
        exact Subtype.ext (frameGeneratorIndex_involutive p j.1)
      right_inv := by
        intro j
        exact Subtype.ext (frameGeneratorIndex_involutive p j.1) }
  unfold btExcessEnergy unitDefectEnergy
  congr 1
  simpa only [Fintype.card_coe] using Fintype.card_congr violatedEquiv

/-- Relabel every increment of a Pauli path. -/
def framePath {L : Nat} [NeZero L] (p : Plane)
    (gamma : PauliErrorPath (ι := Plaquette L)) :
    PauliErrorPath (ι := Plaquette L) where
  increments := gamma.increments.map (frameBinary p)
  step_weight_le_one := by
    intro step hstep
    rw [List.mem_map] at hstep
    obtain ⟨original, horiginal, rfl⟩ := hstep
    rw [weight_frameBinary]
    exact gamma.step_weight_le_one original horiginal

@[simp] theorem framePath_increments {L : Nat} [NeZero L]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) :
    (framePath p gamma).increments = gamma.increments.map (frameBinary p) := rfl

theorem accumulate_frameBinary {L : Nat} [NeZero L]
    (p : Plane) (steps : List (Binary (Plaquette L))) :
    PauliErrorPath.accumulate (steps.map (frameBinary p)) =
      frameBinary p (PauliErrorPath.accumulate steps) := by
  induction steps with
  | nil => simp [PauliErrorPath.accumulate]
  | cons step rest ih =>
      simp only [List.map_cons]
      rw [show PauliErrorPath.accumulate (step :: rest) =
          binaryMul step (PauliErrorPath.accumulate rest) by
        simp only [PauliErrorPath.accumulate, List.foldl_cons, binaryMul_binaryOne_left]
        exact PauliErrorPath.foldl_binaryMul_eq_binaryMul_accumulate rest step]
      rw [show PauliErrorPath.accumulate
          (frameBinary p step :: List.map (frameBinary p) rest) =
          binaryMul (frameBinary p step)
            (PauliErrorPath.accumulate (List.map (frameBinary p) rest)) by
        simp only [PauliErrorPath.accumulate, List.foldl_cons, binaryMul_binaryOne_left]
        exact PauliErrorPath.foldl_binaryMul_eq_binaryMul_accumulate
          (List.map (frameBinary p) rest) (frameBinary p step)]
      rw [ih, ← frameBinary_binaryMul]

@[simp] theorem framePath_endpoint {L : Nat} [NeZero L]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) :
    (framePath p gamma).endpoint = frameBinary p gamma.endpoint := by
  exact accumulate_frameBinary p gamma.increments

@[simp] theorem framePath_stateAt {L : Nat} [NeZero L]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) (n : Nat) :
    (framePath p gamma).stateAt n = frameBinary p (gamma.stateAt n) := by
  change PauliErrorPath.accumulate
      ((gamma.increments.map (frameBinary p)).take n) =
    frameBinary p (PauliErrorPath.accumulate (gamma.increments.take n))
  rw [← List.map_take]
  exact accumulate_frameBinary p (gamma.increments.take n)

/-- Path height is invariant under coordinate framing. -/
theorem pathHeight_framePath {L : Nat} [NeZero L] [Fact (1 < L)]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) :
    (toricHamiltonian (L := L)).pathHeight (framePath p gamma) =
      (toricHamiltonian (L := L)).pathHeight gamma := by
  unfold pathHeight
  simp only [framePath_increments, List.length_map]
  congr 1
  funext n
  rw [framePath_stateAt, btExcessEnergy_frameBinary]

/-! ## The six coordinate membrane basis sectors -/

/-- The primal membrane in plane `p`, at fixed local complementary coordinates. -/
def primalCoordinateMembrane {L : Nat} [NeZero L]
    (p : Plane) (u v : ZMod L) : Word (ZMod 2) (Plaquette L) :=
  framePlaquetteWord p (primalXYMembrane u v)

/-- The dual membrane paired with the primal membrane in plane `p`. -/
def dualCoordinateMembrane {L : Nat} [NeZero L]
    (p : Plane) (u v : ZMod L) : Word (ZMod 2) (Plaquette L) :=
  framePlaquetteWord p (dualXYMembrane u v)

private theorem coord4_eta_frame {L : Nat} (c : Coord L) :
    coord4 (c .x) (c .y) (c .z) (c .w) = c := by
  ext a
  cases a <;> rfl

@[simp] theorem planeFrame_eq_xy_iff (p q : Plane) :
    planeFrame p q = .xy ↔ q = p := by
  cases p <;> cases q <;> decide

theorem primalCoordinateMembrane_apply_eq_zero_of_plane_ne
    {L : Nat} [NeZero L] (p : Plane) (u v : ZMod L)
    (c : Coord L) (q : Plane) (hqp : q ≠ p) :
    primalCoordinateMembrane p u v (c, q) = 0 := by
  rw [primalCoordinateMembrane, framePlaquetteWord_apply]
  change primalXYMembrane u v (frameCoord p c, planeFrame p q) = 0
  rw [← coord4_eta_frame (frameCoord p c), primalXYMembrane_apply_coord4]
  simp [hqp, planeFrame_eq_xy_iff]

theorem dualCoordinateMembrane_apply_eq_zero_of_plane_ne
    {L : Nat} [NeZero L] (p : Plane) (u v : ZMod L)
    (c : Coord L) (q : Plane) (hqp : q ≠ p) :
    dualCoordinateMembrane p u v (c, q) = 0 := by
  rw [dualCoordinateMembrane, framePlaquetteWord_apply]
  change dualXYMembrane u v (frameCoord p c, planeFrame p q) = 0
  rw [← coord4_eta_frame (frameCoord p c), dualXYMembrane_apply_coord4]
  simp [hqp, planeFrame_eq_xy_iff]

/-- The six framed primal/dual membrane pairs have the Kronecker pairing. -/
theorem wordPairing_dualCoordinate_primalCoordinate
    {L : Nat} [NeZero L]
    (p q : Plane) (a b c d : ZMod L) :
    wordPairing (dualCoordinateMembrane p a b)
      (primalCoordinateMembrane q c d) = if p = q then 1 else 0 := by
  by_cases hpq : p = q
  · subst q
    simp only [dualCoordinateMembrane, primalCoordinateMembrane]
    rw [wordPairing_framePlaquetteWord, wordPairing_dual_primal]
    simp
  · rw [if_neg hpq, wordPairing_apply, dotProduct]
    apply Finset.sum_eq_zero
    intro cell _hcell
    rcases cell with ⟨x, r⟩
    by_cases hrp : r = p
    · subst r
      have hzero := primalCoordinateMembrane_apply_eq_zero_of_plane_ne
        q c d x p hpq
      rw [hzero]
      simp
    · have hzero := dualCoordinateMembrane_apply_eq_zero_of_plane_ne
        p a b x r hrp
      rw [hzero]
      simp

/-- A membrane sector is a nonzero `F_2` coefficient vector on the six planes. -/
abbrev MembraneSector := {s : Finset Plane // s.Nonempty}

/-- Canonical primal representative of a nonzero membrane sector. -/
def primalSectorMembrane {L : Nat} [NeZero L] (s : MembraneSector) :
    Word (ZMod 2) (Plaquette L) :=
  ∑ p ∈ s.1, primalCoordinateMembrane p 0 0

/-- Canonical dual representative of a nonzero membrane sector. -/
def dualSectorMembrane {L : Nat} [NeZero L] (s : MembraneSector) :
    Word (ZMod 2) (Plaquette L) :=
  ∑ p ∈ s.1, dualCoordinateMembrane p 0 0

/-- A path ending in a specified nonzero primal membrane homology sector. -/
def HasPrimalSectorEndpoint {L : Nat} [NeZero L]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector) : Prop :=
  ∃ c : Word (ZMod 2) (Cube L),
    gamma.endpoint.vector.zPart = primalSectorMembrane s + boundary3 c

/-- A path ending in a specified nonzero dual membrane cohomology sector. -/
def HasDualSectorEndpoint {L : Nat} [NeZero L]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector) : Prop :=
  ∃ e : Word (ZMod 2) (Link L),
    gamma.endpoint.vector.xPart =
      dualSectorMembrane s + wordLinearMapTranspose boundary2 e

theorem primalSectorMembrane_pairing
    {L : Nat} [NeZero L] (s : MembraneSector) (p : Plane) (hp : p ∈ s.1)
    (a b : ZMod L) :
    wordPairing (dualCoordinateMembrane p a b) (primalSectorMembrane s) = 1 := by
  simp only [primalSectorMembrane, map_sum]
  rw [Finset.sum_eq_single p]
  · rw [wordPairing_dualCoordinate_primalCoordinate, if_pos rfl]
  · intro q hq hqp
    rw [wordPairing_dualCoordinate_primalCoordinate, if_neg (Ne.symm hqp)]
  · exact fun h => (h hp).elim

theorem dualSectorMembrane_pairing
    {L : Nat} [NeZero L] (s : MembraneSector) (p : Plane) (hp : p ∈ s.1)
    (a b : ZMod L) :
    wordPairing (dualSectorMembrane s) (primalCoordinateMembrane p a b) = 1 := by
  rw [show wordPairing (dualSectorMembrane s) (primalCoordinateMembrane p a b) =
      wordPairing (primalCoordinateMembrane p a b) (dualSectorMembrane s) by
    simp [wordPairing_apply, dotProduct_comm]]
  simp only [dualSectorMembrane, map_sum]
  rw [Finset.sum_eq_single p]
  · rw [show wordPairing (primalCoordinateMembrane p a b)
        (dualCoordinateMembrane p 0 0) =
        wordPairing (dualCoordinateMembrane p 0 0)
          (primalCoordinateMembrane p a b) by
      simp [wordPairing_apply, dotProduct_comm]]
    rw [wordPairing_dualCoordinate_primalCoordinate, if_pos rfl]
  · intro q hq hqp
    rw [show wordPairing (primalCoordinateMembrane p a b)
        (dualCoordinateMembrane q 0 0) =
        wordPairing (dualCoordinateMembrane q 0 0)
          (primalCoordinateMembrane p a b) by
      simp [wordPairing_apply, dotProduct_comm]]
    rw [wordPairing_dualCoordinate_primalCoordinate, if_neg hqp]
  · exact fun h => (h hp).elim

/-- Every coordinate dual membrane annihilates primal stabilizer boundaries. -/
theorem wordPairing_dualCoordinate_boundary3_zero
    {L : Nat} [NeZero L] (p : Plane) (a b : ZMod L)
    (c : Word (ZMod 2) (Cube L)) :
    wordPairing (dualCoordinateMembrane p a b) (boundary3 c) = 0 := by
  rw [dualCoordinateMembrane, wordPairing_framePlaquetteWord_left,
    frame_boundary3, ← wordPairing_wordLinearMapTranspose,
    transpose_boundary3_dualXYMembrane]
  simp

/-- Every coordinate primal membrane annihilates dual stabilizer coboundaries. -/
theorem wordPairing_transpose_boundary2_primalCoordinate_zero
    {L : Nat} [NeZero L] (p : Plane) (a b : ZMod L)
    (e : Word (ZMod 2) (Link L)) :
    wordPairing (wordLinearMapTranspose boundary2 e)
      (primalCoordinateMembrane p a b) = 0 := by
  rw [show wordPairing (wordLinearMapTranspose boundary2 e)
        (primalCoordinateMembrane p a b) =
      wordPairing (primalCoordinateMembrane p a b)
        (wordLinearMapTranspose boundary2 e) by
    simp [wordPairing_apply, dotProduct_comm]]
  rw [primalCoordinateMembrane, wordPairing_framePlaquetteWord_left,
    frame_transpose_boundary2]
  rw [show wordPairing (primalXYMembrane a b)
        (wordLinearMapTranspose boundary2 (frameLinkWord p e)) =
      wordPairing (wordLinearMapTranspose boundary2 (frameLinkWord p e))
        (primalXYMembrane a b) by
    simp [wordPairing_apply, dotProduct_comm]]
  rw [wordPairing_wordLinearMapTranspose, boundary2_primalXYMembrane]
  simp

/-- A nonempty primal coefficient vector is not a stabilizer boundary. -/
theorem primalSectorMembrane_ne_boundary3
    {L : Nat} [NeZero L] (s : MembraneSector)
    (c : Word (ZMod 2) (Cube L)) :
    primalSectorMembrane s ≠ boundary3 c := by
  obtain ⟨p, hp⟩ := s.2
  intro h
  have hpair := congrArg
    (fun m => wordPairing (dualCoordinateMembrane p 0 0) m) h
  change wordPairing (dualCoordinateMembrane p 0 0)
      (primalSectorMembrane s) =
    wordPairing (dualCoordinateMembrane p 0 0) (boundary3 c) at hpair
  rw [primalSectorMembrane_pairing s p hp,
    wordPairing_dualCoordinate_boundary3_zero] at hpair
  exact one_ne_zero hpair

/-- A nonempty dual coefficient vector is not a stabilizer coboundary. -/
theorem dualSectorMembrane_ne_transpose_boundary2
    {L : Nat} [NeZero L] (s : MembraneSector)
    (e : Word (ZMod 2) (Link L)) :
    dualSectorMembrane s ≠ wordLinearMapTranspose boundary2 e := by
  obtain ⟨p, hp⟩ := s.2
  intro h
  have hpair := congrArg
    (fun m => wordPairing m (primalCoordinateMembrane p 0 0)) h
  change wordPairing (dualSectorMembrane s)
      (primalCoordinateMembrane p 0 0) =
    wordPairing (wordLinearMapTranspose boundary2 e)
      (primalCoordinateMembrane p 0 0) at hpair
  rw [dualSectorMembrane_pairing s p hp,
    wordPairing_transpose_boundary2_primalCoordinate_zero] at hpair
  exact one_ne_zero hpair

theorem primalSectorMembrane_pairing_indicator
    {L : Nat} [NeZero L] (s : MembraneSector) (p : Plane)
    (a b : ZMod L) :
    wordPairing (dualCoordinateMembrane p a b) (primalSectorMembrane s) =
      if p ∈ s.1 then 1 else 0 := by
  by_cases hp : p ∈ s.1
  · rw [if_pos hp, primalSectorMembrane_pairing s p hp]
  · simp only [primalSectorMembrane, map_sum]
    rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q hq
    rw [wordPairing_dualCoordinate_primalCoordinate, if_neg]
    intro hpq
    subst q
    exact hp hq

theorem dualSectorMembrane_pairing_indicator
    {L : Nat} [NeZero L] (s : MembraneSector) (p : Plane)
    (a b : ZMod L) :
    wordPairing (dualSectorMembrane s) (primalCoordinateMembrane p a b) =
      if p ∈ s.1 then 1 else 0 := by
  by_cases hp : p ∈ s.1
  · rw [if_pos hp, dualSectorMembrane_pairing s p hp]
  · rw [show wordPairing (dualSectorMembrane s)
        (primalCoordinateMembrane p a b) =
      wordPairing (primalCoordinateMembrane p a b)
        (dualSectorMembrane s) by
    simp [wordPairing_apply, dotProduct_comm]]
    simp only [dualSectorMembrane, map_sum]
    rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q hq
    rw [show wordPairing (primalCoordinateMembrane p a b)
          (dualCoordinateMembrane q 0 0) =
        wordPairing (dualCoordinateMembrane q 0 0)
          (primalCoordinateMembrane p a b) by
      simp [wordPairing_apply, dotProduct_comm]]
    rw [wordPairing_dualCoordinate_primalCoordinate, if_neg]
    intro hqp
    subst q
    exact hp hq

private theorem exists_plane_mem_xor (s t : MembraneSector) (hst : s ≠ t) :
    ∃ p : Plane,
      (p ∈ s.1 ∧ p ∉ t.1) ∨ (p ∈ t.1 ∧ p ∉ s.1) := by
  have hfin : s.1 ≠ t.1 := by
    intro h
    exact hst (Subtype.ext h)
  by_cases hsub : s.1 ⊆ t.1
  · have hnsub : ¬ t.1 ⊆ s.1 := by
      intro hts
      exact hfin (Finset.Subset.antisymm hsub hts)
    obtain ⟨p, hpt, hps⟩ := Finset.not_subset.mp hnsub
    exact ⟨p, Or.inr ⟨hpt, hps⟩⟩
  · obtain ⟨p, hps, hpt⟩ := Finset.not_subset.mp hsub
    exact ⟨p, Or.inl ⟨hps, hpt⟩⟩

/-- Distinct primal coefficient vectors remain distinct modulo boundaries. -/
theorem primalSectorMembrane_add_ne_boundary3
    {L : Nat} [NeZero L] (s t : MembraneSector) (hst : s ≠ t)
    (c : Word (ZMod 2) (Cube L)) :
    primalSectorMembrane s + primalSectorMembrane t ≠ boundary3 c := by
  obtain ⟨p, hp | hp⟩ := exists_plane_mem_xor s t hst
  · intro h
    have hpair := congrArg
      (fun m => wordPairing (dualCoordinateMembrane p 0 0) m) h
    change wordPairing (dualCoordinateMembrane p 0 0)
        (primalSectorMembrane s + primalSectorMembrane t) =
      wordPairing (dualCoordinateMembrane p 0 0) (boundary3 c) at hpair
    rw [map_add, primalSectorMembrane_pairing_indicator,
      primalSectorMembrane_pairing_indicator,
      wordPairing_dualCoordinate_boundary3_zero] at hpair
    simp [hp.1, hp.2] at hpair
  · intro h
    have hpair := congrArg
      (fun m => wordPairing (dualCoordinateMembrane p 0 0) m) h
    change wordPairing (dualCoordinateMembrane p 0 0)
        (primalSectorMembrane s + primalSectorMembrane t) =
      wordPairing (dualCoordinateMembrane p 0 0) (boundary3 c) at hpair
    rw [map_add, primalSectorMembrane_pairing_indicator,
      primalSectorMembrane_pairing_indicator,
      wordPairing_dualCoordinate_boundary3_zero] at hpair
    simp [hp.1, hp.2] at hpair

/-- Distinct dual coefficient vectors remain distinct modulo coboundaries. -/
theorem dualSectorMembrane_add_ne_transpose_boundary2
    {L : Nat} [NeZero L] (s t : MembraneSector) (hst : s ≠ t)
    (e : Word (ZMod 2) (Link L)) :
    dualSectorMembrane s + dualSectorMembrane t ≠
      wordLinearMapTranspose boundary2 e := by
  obtain ⟨p, hp | hp⟩ := exists_plane_mem_xor s t hst
  · intro h
    have hpair := congrArg
      (fun m => wordPairing m (primalCoordinateMembrane p 0 0)) h
    change wordPairing (dualSectorMembrane s + dualSectorMembrane t)
        (primalCoordinateMembrane p 0 0) =
      wordPairing (wordLinearMapTranspose boundary2 e)
        (primalCoordinateMembrane p 0 0) at hpair
    rw [map_add] at hpair
    change wordPairing (dualSectorMembrane s) (primalCoordinateMembrane p 0 0) +
        wordPairing (dualSectorMembrane t) (primalCoordinateMembrane p 0 0) =
      wordPairing (wordLinearMapTranspose boundary2 e)
        (primalCoordinateMembrane p 0 0) at hpair
    rw [dualSectorMembrane_pairing_indicator,
      dualSectorMembrane_pairing_indicator,
      wordPairing_transpose_boundary2_primalCoordinate_zero] at hpair
    simp [hp.1, hp.2] at hpair
  · intro h
    have hpair := congrArg
      (fun m => wordPairing m (primalCoordinateMembrane p 0 0)) h
    change wordPairing (dualSectorMembrane s + dualSectorMembrane t)
        (primalCoordinateMembrane p 0 0) =
      wordPairing (wordLinearMapTranspose boundary2 e)
        (primalCoordinateMembrane p 0 0) at hpair
    rw [map_add] at hpair
    change wordPairing (dualSectorMembrane s) (primalCoordinateMembrane p 0 0) +
        wordPairing (dualSectorMembrane t) (primalCoordinateMembrane p 0 0) =
      wordPairing (wordLinearMapTranspose boundary2 e)
        (primalCoordinateMembrane p 0 0) at hpair
    rw [dualSectorMembrane_pairing_indicator,
      dualSectorMembrane_pairing_indicator,
      wordPairing_transpose_boundary2_primalCoordinate_zero] at hpair
    simp [hp.1, hp.2] at hpair

theorem primalSquareProjection_frame_primalSectorMembrane
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (s : MembraneSector) (p : Plane) (hp : p ∈ s.1) :
    primalSquareProjection (framePlaquetteWord p (primalSectorMembrane s)) =
      (fun _ _ => 1 : BinarySquare.Grid L) := by
  funext y x
  rw [primalSquareProjection]
  rw [show wordPairing (dualXYMembrane (finToPeriodic x) (finToPeriodic y))
        (framePlaquetteWord p (primalSectorMembrane s)) =
      wordPairing
        (framePlaquetteWord p
          (dualXYMembrane (finToPeriodic x) (finToPeriodic y)))
        (primalSectorMembrane s) by
    exact (wordPairing_framePlaquetteWord_left p _ _).symm]
  exact primalSectorMembrane_pairing s p hp _ _

theorem dualSquareProjection_frame_dualSectorMembrane
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (s : MembraneSector) (p : Plane) (hp : p ∈ s.1) :
    dualSquareProjection (framePlaquetteWord p (dualSectorMembrane s)) =
      (fun _ _ => 1 : BinarySquare.Grid L) := by
  funext w z
  rw [dualSquareProjection, wordPairing_framePlaquetteWord_left]
  exact dualSectorMembrane_pairing s p hp _ _

theorem primalSquareProjection_boundary3_zero {L : Nat}
    [NeZero L] [Fact (1 < L)]
    (c : Word (ZMod 2) (Cube L)) :
    primalSquareProjection (boundary3 c) = (0 : BinarySquare.Grid L) := by
  funext y x
  rw [primalSquareProjection, ← wordPairing_wordLinearMapTranspose,
    transpose_boundary3_dualXYMembrane (L := L)]
  simp

theorem dualSquareProjection_transpose_boundary2_zero {L : Nat}
    [NeZero L] [Fact (1 < L)]
    (e : Word (ZMod 2) (Link L)) :
    dualSquareProjection (wordLinearMapTranspose boundary2 e) =
      (0 : BinarySquare.Grid L) := by
  funext w z
  rw [dualSquareProjection, wordPairing_wordLinearMapTranspose,
    boundary2_primalXYMembrane (L := L)]
  simp

theorem primalProjectionEndpoint_of_hasPrimalSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector)
    (p : Plane) (hp : p ∈ s.1) (hendpoint : HasPrimalSectorEndpoint gamma s) :
    primalSquareProjection
      ((framePath p gamma).endpoint.vector.zPart) = fun _ _ => 1 := by
  rcases hendpoint with ⟨c, hc⟩
  rw [framePath_endpoint, frameBinary_zPart, hc, map_add,
    frame_boundary3, primalSquareProjection_add,
    primalSquareProjection_frame_primalSectorMembrane s p hp,
    primalSquareProjection_boundary3_zero]
  simp

theorem dualProjectionEndpoint_of_hasDualSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector)
    (p : Plane) (hp : p ∈ s.1) (hendpoint : HasDualSectorEndpoint gamma s) :
    dualSquareProjection
      ((framePath p gamma).endpoint.vector.xPart) = fun _ _ => 1 := by
  rcases hendpoint with ⟨e, he⟩
  rw [framePath_endpoint, frameBinary_xPart, he, map_add,
    frame_transpose_boundary2, dualSquareProjection_add,
    dualSquareProjection_frame_dualSectorMembrane s p hp,
    dualSquareProjection_transpose_boundary2_zero]
  simp

/-- The #569 separator proof only needs an all-one primal endpoint projection. -/
theorem half_le_pathHeight_of_primalProjectionEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L))
    (hendpoint : primalSquareProjection gamma.endpoint.vector.zPart =
      fun _ _ => 1) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight gamma := by
  have hcount : primalFullRowCount gamma gamma.increments.length = L := by
    rw [primalFullRowCount, gamma.stateAt_length, hendpoint]
    simp [BinarySquare.fullRows]
  obtain ⟨n, hn, hhalf⟩ := BinarySquare.exists_eq_of_nat_walk
    (primalFullRowCount gamma) gamma.increments.length (L / 2)
    (by simp) (by rw [hcount]; omega)
    (fun n hn => primalFullRowCount_dist_succ_le_one gamma n hn)
  have hseparator :=
    BinarySquare.half_le_openBoundaryLength_of_fullRows_card
      (primalSquareProjection (gamma.stateAt n).vector.zPart) (by
        simpa [primalFullRowCount] using hhalf)
  exact (hseparator.trans
    (primal_openBoundaryLength_le_two_mul_loopLength
      (gamma.stateAt n).vector.zPart)).trans
        ((two_mul_primalLoopLength_le_btExcessEnergy (gamma.stateAt n)).trans
          ((toricHamiltonian (L := L)).btExcessEnergy_stateAt_le_pathHeight
            gamma n hn))

/-- The #569 separator proof only needs an all-one dual endpoint projection. -/
theorem half_le_pathHeight_of_dualProjectionEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L))
    (hendpoint : dualSquareProjection gamma.endpoint.vector.xPart =
      fun _ _ => 1) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight gamma := by
  have hcount : dualFullRowCount gamma gamma.increments.length = L := by
    rw [dualFullRowCount, gamma.stateAt_length, hendpoint]
    simp [BinarySquare.fullRows]
  obtain ⟨n, hn, hhalf⟩ := BinarySquare.exists_eq_of_nat_walk
    (dualFullRowCount gamma) gamma.increments.length (L / 2)
    (by simp) (by rw [hcount]; omega)
    (fun n hn => dualFullRowCount_dist_succ_le_one gamma n hn)
  have hseparator :=
    BinarySquare.half_le_openBoundaryLength_of_fullRows_card
      (dualSquareProjection (gamma.stateAt n).vector.xPart) (by
        simpa [dualFullRowCount] using hhalf)
  exact (hseparator.trans
    (dual_openBoundaryLength_le_two_mul_loopLength
      (gamma.stateAt n).vector.xPart)).trans
        ((two_mul_dualLoopLength_le_btExcessEnergy (gamma.stateAt n)).trans
          ((toricHamiltonian (L := L)).btExcessEnergy_stateAt_le_pathHeight
            gamma n hn))

/-- Every path to every nonzero primal coordinate-membrane sector has linear height. -/
theorem half_le_pathHeight_of_hasPrimalSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector)
    (hendpoint : HasPrimalSectorEndpoint gamma s) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight gamma := by
  obtain ⟨p, hp⟩ := s.2
  rw [← pathHeight_framePath p gamma]
  exact half_le_pathHeight_of_primalProjectionEndpoint (framePath p gamma)
    (primalProjectionEndpoint_of_hasPrimalSectorEndpoint gamma s p hp hendpoint)

/-- Every path to every nonzero dual coordinate-membrane sector has linear height. -/
theorem half_le_pathHeight_of_hasDualSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector)
    (hendpoint : HasDualSectorEndpoint gamma s) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight gamma := by
  obtain ⟨p, hp⟩ := s.2
  rw [← pathHeight_framePath p gamma]
  exact half_le_pathHeight_of_dualProjectionEndpoint (framePath p gamma)
    (dualProjectionEndpoint_of_hasDualSectorEndpoint gamma s p hp hendpoint)

/-! ## Explicit sweeps for every nonzero sector -/

/-- Path height is subadditive when two actual single-qubit paths are concatenated. -/
theorem toric_pathHeight_append_le_add {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma delta : PauliErrorPath (ι := Plaquette L)) :
    (toricHamiltonian (L := L)).pathHeight (gamma.append delta) ≤
      (toricHamiltonian (L := L)).pathHeight gamma +
        (toricHamiltonian (L := L)).pathHeight delta := by
  rw [pathHeight]
  apply Finset.sup_le
  intro n hn
  have hnTotal : n ≤ gamma.increments.length + delta.increments.length := by
    have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simpa using this
  by_cases hnLeft : n ≤ gamma.increments.length
  · rw [PauliErrorPath.stateAt_append_left gamma delta n hnLeft]
    exact le_trans
      ((toricHamiltonian (L := L)).btExcessEnergy_stateAt_le_pathHeight
        gamma n hnLeft)
      (Nat.le_add_right _ _)
  · let k := n - gamma.increments.length
    have hnk : n = gamma.increments.length + k := by
      dsimp [k]
      omega
    have hk : k ≤ delta.increments.length := by
      dsimp [k]
      omega
    rw [hnk, PauliErrorPath.stateAt_append_right]
    exact le_trans
      ((toricHamiltonian (L := L)).btExcessEnergy_binaryMul_le
        gamma.endpoint (delta.stateAt k))
      (Nat.add_le_add
        ((toricHamiltonian (L := L)).btExcessEnergy_endpoint_le_pathHeight gamma)
        ((toricHamiltonian (L := L)).btExcessEnergy_stateAt_le_pathHeight
          delta k hk))

/-- Concatenate a finite list of actual Pauli paths in the listed order. -/
def appendMembranePaths {L : Nat} [NeZero L] [Fact (1 < L)] :
    List (PauliErrorPath (ι := Plaquette L)) → PauliErrorPath (ι := Plaquette L)
  | [] => PauliErrorPath.empty
  | gamma :: rest => gamma.append (appendMembranePaths rest)

/-- The canonical sweep of the primal membrane in coordinate plane `p`. -/
def primalCoordinateSweepPath {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    PauliErrorPath (ι := Plaquette L) :=
  framePath p (primalMembraneSweepPath 0 0)

/-- The canonical sweep of the dual membrane in coordinate plane `p`. -/
def dualCoordinateSweepPath {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    PauliErrorPath (ι := Plaquette L) :=
  framePath p (dualMembraneSweepPath 0 0)

@[simp] theorem primalCoordinateSweepPath_endpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    (primalCoordinateSweepPath (L := L) p).endpoint =
      cssZCheck (primalCoordinateMembrane p 0 0) := by
  simp [primalCoordinateSweepPath, primalCoordinateMembrane,
    primalMembraneError]

@[simp] theorem dualCoordinateSweepPath_endpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    (dualCoordinateSweepPath (L := L) p).endpoint =
      cssXCheck (dualCoordinateMembrane p 0 0) := by
  simp [dualCoordinateSweepPath, dualCoordinateMembrane,
    dualMembraneError]

theorem endpoint_appendPrimalSweepList
    {L : Nat} [NeZero L] [Fact (1 < L)] (planes : List Plane) :
    (appendMembranePaths
      (planes.map (primalCoordinateSweepPath (L := L)))).endpoint =
      cssZCheck ((planes.map
        (fun p => primalCoordinateMembrane (L := L) p 0 0)).sum) := by
  induction planes with
  | nil => rfl
  | cons p planes ih =>
      simp [appendMembranePaths, PauliErrorPath.endpoint_append, ih]

theorem endpoint_appendDualSweepList
    {L : Nat} [NeZero L] [Fact (1 < L)] (planes : List Plane) :
    (appendMembranePaths
      (planes.map (dualCoordinateSweepPath (L := L)))).endpoint =
      cssXCheck ((planes.map
        (fun p => dualCoordinateMembrane (L := L) p 0 0)).sum) := by
  induction planes with
  | nil => rfl
  | cons p planes ih =>
      simp [appendMembranePaths, PauliErrorPath.endpoint_append, ih]

/-- Concatenated primal basis sweeps realize the requested coefficient vector. -/
def primalSectorSweepPath {L : Nat} [NeZero L] [Fact (1 < L)]
    (s : MembraneSector) :
    PauliErrorPath (ι := Plaquette L) :=
  appendMembranePaths
    (s.1.toList.map (primalCoordinateSweepPath (L := L)))

/-- Concatenated dual basis sweeps realize the requested coefficient vector. -/
def dualSectorSweepPath {L : Nat} [NeZero L] [Fact (1 < L)]
    (s : MembraneSector) :
    PauliErrorPath (ι := Plaquette L) :=
  appendMembranePaths
    (s.1.toList.map (dualCoordinateSweepPath (L := L)))

@[simp] theorem primalSectorSweepPath_endpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    (primalSectorSweepPath (L := L) s).endpoint =
      cssZCheck (primalSectorMembrane s) := by
  rw [primalSectorSweepPath, endpoint_appendPrimalSweepList]
  congr 1
  simp [primalSectorMembrane]

@[simp] theorem dualSectorSweepPath_endpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    (dualSectorSweepPath (L := L) s).endpoint =
      cssXCheck (dualSectorMembrane s) := by
  rw [dualSectorSweepPath, endpoint_appendDualSweepList]
  congr 1
  simp [dualSectorMembrane]

theorem pathHeight_primalCoordinateSweepPath_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    (toricHamiltonian (L := L)).pathHeight
      (primalCoordinateSweepPath (L := L) p) ≤ 64 * L := by
  rw [primalCoordinateSweepPath, pathHeight_framePath]
  exact pathHeight_primalMembraneSweepPath_le 0 0

theorem pathHeight_dualCoordinateSweepPath_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    (toricHamiltonian (L := L)).pathHeight
      (dualCoordinateSweepPath (L := L) p) ≤ 64 * L := by
  rw [dualCoordinateSweepPath, pathHeight_framePath]
  exact pathHeight_dualMembraneSweepPath_le 0 0

theorem pathHeight_appendPrimalSweepList_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (planes : List Plane) :
    (toricHamiltonian (L := L)).pathHeight
      (appendMembranePaths
        (planes.map (primalCoordinateSweepPath (L := L)))) ≤
      planes.length * (64 * L) := by
  induction planes with
  | nil => simp [appendMembranePaths]
  | cons p planes ih =>
      calc
        _ ≤ (toricHamiltonian (L := L)).pathHeight
              (primalCoordinateSweepPath (L := L) p) +
            (toricHamiltonian (L := L)).pathHeight
              (appendMembranePaths
                (planes.map (primalCoordinateSweepPath (L := L)))) := by
              simpa [appendMembranePaths] using
                toric_pathHeight_append_le_add
                  (primalCoordinateSweepPath (L := L) p)
                  (appendMembranePaths
                    (planes.map (primalCoordinateSweepPath (L := L))))
        _ ≤ 64 * L + planes.length * (64 * L) :=
          Nat.add_le_add (pathHeight_primalCoordinateSweepPath_le p) ih
        _ = (p :: planes).length * (64 * L) := by
          simp only [List.length_cons]
          ring

theorem pathHeight_appendDualSweepList_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (planes : List Plane) :
    (toricHamiltonian (L := L)).pathHeight
      (appendMembranePaths
        (planes.map (dualCoordinateSweepPath (L := L)))) ≤
      planes.length * (64 * L) := by
  induction planes with
  | nil => simp [appendMembranePaths]
  | cons p planes ih =>
      calc
        _ ≤ (toricHamiltonian (L := L)).pathHeight
              (dualCoordinateSweepPath (L := L) p) +
            (toricHamiltonian (L := L)).pathHeight
              (appendMembranePaths
                (planes.map (dualCoordinateSweepPath (L := L)))) := by
              simpa [appendMembranePaths] using
                toric_pathHeight_append_le_add
                  (dualCoordinateSweepPath (L := L) p)
                  (appendMembranePaths
                    (planes.map (dualCoordinateSweepPath (L := L))))
        _ ≤ 64 * L + planes.length * (64 * L) :=
          Nat.add_le_add (pathHeight_dualCoordinateSweepPath_le p) ih
        _ = (p :: planes).length * (64 * L) := by
          simp only [List.length_cons]
          ring

private theorem membraneSector_card_le_six (s : MembraneSector) :
    s.1.card ≤ 6 := by
  calc
    s.1.card ≤ Fintype.card Plane := Finset.card_le_univ _
    _ = 6 := by decide

/-- Every nonzero primal sector has an explicit sweep of height at most `384 L`. -/
theorem pathHeight_primalSectorSweepPath_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    (toricHamiltonian (L := L)).pathHeight
      (primalSectorSweepPath (L := L) s) ≤ 384 * L := by
  calc
    _ ≤ s.1.toList.length * (64 * L) :=
      pathHeight_appendPrimalSweepList_le s.1.toList
    _ ≤ 6 * (64 * L) := by
      exact Nat.mul_le_mul_right (64 * L) (by
        simpa using membraneSector_card_le_six s)
    _ = 384 * L := by ring

/-- Every nonzero dual sector has an explicit sweep of height at most `384 L`. -/
theorem pathHeight_dualSectorSweepPath_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    (toricHamiltonian (L := L)).pathHeight
      (dualSectorSweepPath (L := L) s) ≤ 384 * L := by
  calc
    _ ≤ s.1.toList.length * (64 * L) :=
      pathHeight_appendDualSweepList_le s.1.toList
    _ ≤ 6 * (64 * L) := by
      exact Nat.mul_le_mul_right (64 * L) (by
        simpa using membraneSector_card_le_six s)
    _ = 384 * L := by ring

theorem primalSectorSweepPath_hasPrimalSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    HasPrimalSectorEndpoint (primalSectorSweepPath (L := L) s) s := by
  refine ⟨0, ?_⟩
  simp

theorem dualSectorSweepPath_hasDualSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    HasDualSectorEndpoint (dualSectorSweepPath (L := L) s) s := by
  refine ⟨0, ?_⟩
  simp

/-- There are exactly `2^6 - 1 = 63` nonzero coordinate-membrane sectors. -/
theorem card_membraneSector : Fintype.card MembraneSector = 63 := by
  decide

set_option maxHeartbeats 200000

end QEC.Coding.PeriodicCubical4
