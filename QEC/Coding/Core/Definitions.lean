import QEC.Semantics.Core.Definitions
/-!
# QEC.Coding

Coding-theoretic structures for algebraic, stabilizer, CSS, homological, and
LDPC code formalizations.
-/

namespace QEC
namespace Coding

universe u v w x

/-- The ambient word space for a code over alphabet `F` and coordinate set `ι`. -/
abbrev Word (F : Type u) (ι : Type v) := ι → F

/-- The construction-independent unit basis word.  Its implementation fixes
the equality decider internally so public theorem statements do not depend on
a particular `DecidableEq` instance for the coordinate type. -/
noncomputable def canonicalBasisWord
    {F : Type u} {ι : Type v} [Zero F] [One F] (i : ι) : Word F ι := by
  classical
  exact Pi.single i 1

/-- The project-selected finite-coordinate dot-product pairing on words. -/
def wordPairing {F : Type u} {ι : Type v} [Field F] [Fintype ι] :
    LinearMap.BilinForm F (Word F ι) where
  toFun x :=
    { toFun := fun y => dotProduct x y
      map_add' := by
        intro y z
        exact dotProduct_add x y z
      map_smul' := by
        intro a y
        exact dotProduct_smul a x y }
  map_add' := by
    intro x y
    ext z
    exact add_dotProduct x y z
  map_smul' := by
    intro a x
    ext y
    exact smul_dotProduct a x y

@[simp]
theorem wordPairing_apply {F : Type u} {ι : Type v} [Field F] [Fintype ι]
    (x y : Word F ι) :
    wordPairing (F := F) (ι := ι) x y = dotProduct x y :=
  rfl

/-- The finite-coordinate dot-product pairing separates both word arguments. -/
theorem wordPairing_nondegenerate {F : Type u} {ι : Type v} [Field F] [Fintype ι] :
    (wordPairing (F := F) (ι := ι)).Nondegenerate := by
  constructor
  · intro x hx
    exact dotProduct_eq_zero_iff.mp (fun y => by simpa [wordPairing_apply] using hx y)
  · intro y hy
    exact dotProduct_eq_zero_iff.mp (fun x => by
      rw [dotProduct_comm]
      simpa [wordPairing_apply] using hy x)

theorem word_eq_sum_single {F : Type u} {ι : Type v} [Field F] [Fintype ι]
    [DecidableEq ι] (x : Word F ι) :
    (Finset.univ.sum fun i : ι => Pi.single i (x i) : Word F ι) = x :=
  LinearMap.sum_single_apply (fun _ : ι => F) x

/--
The transpose of a finite-coordinate linear map under the project-selected word
pairing.
-/
noncomputable def wordLinearMapTranspose
    {F : Type u} {ι : Type v} {κ : Type w} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (A : Word F ι →ₗ[F] Word F κ) : Word F κ →ₗ[F] Word F ι := by
  classical
  exact
    { toFun := fun y i =>
        Finset.univ.sum fun k : κ => y k * A (Pi.single i (1 : F) : Word F ι) k
      map_add' := by
        intro y z
        ext i
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a y
        ext i
        simp [Finset.mul_sum, mul_assoc] }

theorem wordPairing_wordLinearMapTranspose
    {F : Type u} {ι : Type v} {κ : Type w} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (A : Word F ι →ₗ[F] Word F κ) (y : Word F κ) (x : Word F ι) :
    wordPairing (F := F) (ι := ι) (wordLinearMapTranspose A y) x =
      wordPairing (F := F) (ι := κ) y (A x) := by
  classical
  have hA :
      A x = Finset.univ.sum fun i : ι => x i • A (Pi.single i (1 : F) : Word F ι) := by
    calc
      A x = A (Finset.univ.sum fun i : ι =>
          (Pi.single i (x i) : Word F ι)) := by
        rw [word_eq_sum_single (F := F) x]
      _ = Finset.univ.sum fun i : ι =>
          A (Pi.single i (x i) : Word F ι) := by
        rw [map_sum]
      _ = Finset.univ.sum fun i : ι => x i • A (Pi.single i (1 : F) : Word F ι) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← map_smul]
        congr 1
        rw [← Pi.single_smul]
        simp
  have hA_apply (k : κ) :
      A x k = Finset.univ.sum fun i : ι =>
        x i * A (Pi.single i (1 : F) : Word F ι) k := by
    rw [hA]
    simp [Pi.smul_apply]
  calc
    wordPairing (F := F) (ι := ι) (wordLinearMapTranspose A y) x
        = Finset.univ.sum fun i : ι =>
            (Finset.univ.sum fun k : κ =>
              y k * A (Pi.single i (1 : F) : Word F ι) k) * x i := by
          simp [wordPairing_apply, wordLinearMapTranspose, dotProduct]
    _ = Finset.univ.sum fun i : ι =>
          Finset.univ.sum fun k : κ =>
            (y k * A (Pi.single i (1 : F) : Word F ι) k) * x i := by
          simp [Finset.sum_mul]
    _ = Finset.univ.sum fun k : κ =>
          Finset.univ.sum fun i : ι =>
            (y k * A (Pi.single i (1 : F) : Word F ι) k) * x i := by
          rw [Finset.sum_comm]
    _ = Finset.univ.sum fun k : κ =>
          y k * (Finset.univ.sum fun i : ι =>
            x i * A (Pi.single i (1 : F) : Word F ι) k) := by
          apply Finset.sum_congr rfl
          intro k _
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ = Finset.univ.sum fun k : κ => y k * A x k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← hA_apply k]
    _ = wordPairing (F := F) (ι := κ) y (A x) := by
          simp [wordPairing_apply, dotProduct]

/--
A linear code over a finite field.

The coordinate type `ι` is finite, so `Word F ι` is the finite-length ambient
space, and the code carrier is an `F`-linear subspace of that ambient space.
-/
structure LinearCode (F : Type u) (ι : Type v) [Field F] [Fintype F] [Fintype ι] where
  carrier : Submodule F (Word F ι)

namespace LinearCode

variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

instance : Coe (LinearCode F ι) (Submodule F (Word F ι)) where
  coe C := C.carrier

/-- Membership in a linear code is membership in its carrier submodule. -/
theorem mem_carrier (C : LinearCode F ι) (x : Word F ι) :
    x ∈ C.carrier ↔ x ∈ (C : Submodule F (Word F ι)) :=
  Iff.rfl

/-- The dual linear code under the project-selected finite-coordinate pairing. -/
def dual (C : LinearCode F ι) : LinearCode F ι where
  carrier := (LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))).orthogonal C.carrier

@[simp]
theorem dual_carrier (C : LinearCode F ι) :
    (C.dual).carrier =
      (LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))).orthogonal C.carrier :=
  rfl

/--
Membership in the dual code is exactly orthogonality to every codeword under
the finite-coordinate pairing.
-/
theorem mem_dual (C : LinearCode F ι) (x : Word F ι) :
    x ∈ C.dual.carrier ↔
      ∀ c : Word F ι, c ∈ C.carrier → wordPairing (F := F) (ι := ι) x c = 0 := by
  simp [dual, LinearMap.BilinForm.isOrtho_def, LinearMap.BilinForm.flip_apply]

/-- A word in the dual is orthogonal to every codeword. -/
theorem orthogonal_of_mem_dual (C : LinearCode F ι) {x c : Word F ι}
    (hx : x ∈ C.dual.carrier) (hc : c ∈ C.carrier) :
    wordPairing (F := F) (ι := ι) x c = 0 :=
  (C.mem_dual x).1 hx c hc

/-- Codewords are orthogonal to words in the dual under the symmetric pairing. -/
theorem dual_orthogonal (C : LinearCode F ι) {c x : Word F ι}
    (hc : c ∈ C.carrier) (hx : x ∈ C.dual.carrier) :
    wordPairing (F := F) (ι := ι) c x = 0 := by
  rw [wordPairing_apply, dotProduct_comm]
  exact C.orthogonal_of_mem_dual hx hc

/-- Dual containment is symmetric for finite-coordinate linear codes. -/
theorem le_dual_of_le_dual (C D : LinearCode F ι)
    (h : D.carrier ≤ C.dual.carrier) :
    C.carrier ≤ D.dual.carrier := by
  intro c hc
  refine (D.mem_dual c).2 ?_
  intro d hd
  exact C.dual_orthogonal hc (h hd)

/-- Dual containment between finite-coordinate linear codes is symmetric. -/
theorem le_dual_iff_le_dual (C D : LinearCode F ι) :
    D.carrier ≤ C.dual.carrier ↔ C.carrier ≤ D.dual.carrier := by
  constructor
  · exact le_dual_of_le_dual C D
  · exact le_dual_of_le_dual D C

end LinearCode

/-- The finite set of coordinates where a word is nonzero. -/
def hammingSupport {F : Type u} {ι : Type v} [Zero F] [DecidableEq F] [Fintype ι]
    (x : Word F ι) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ 0

/-- Hamming weight: the number of nonzero coordinates in a word. -/
def HammingWeight {F : Type u} {ι : Type v} [Zero F] [DecidableEq F] [Fintype ι]
    (x : Word F ι) : Nat :=
  (hammingSupport x).card

@[simp]
theorem HammingWeight_eq_card_hammingSupport {F : Type u} {ι : Type v} [Zero F]
    [DecidableEq F] [Fintype ι] (x : Word F ι) :
    HammingWeight x = (hammingSupport x).card :=
  rfl

@[simp]
theorem hammingSupport_zero {F : Type u} {ι : Type v} [Zero F] [DecidableEq F]
    [Fintype ι] :
    hammingSupport (0 : Word F ι) = ∅ := by
  ext i
  simp [hammingSupport]

@[simp]
theorem HammingWeight_zero {F : Type u} {ι : Type v} [Zero F] [DecidableEq F]
    [Fintype ι] :
    HammingWeight (0 : Word F ι) = 0 := by
  simp [HammingWeight]

@[simp]
theorem HammingWeight_eq_zero_iff {F : Type u} {ι : Type v} [Zero F]
    [DecidableEq F] [Fintype ι] (x : Word F ι) :
    HammingWeight x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    by_contra hxi
    have hxi0 : x i ≠ 0 := by
      simpa using hxi
    have hi : i ∈ hammingSupport x := by
      simp [hammingSupport, hxi0]
    have hcard : (hammingSupport x).card = 0 := by
      simpa [HammingWeight] using hx
    have hempty : hammingSupport x = ∅ := Finset.card_eq_zero.mp hcard
    have hnot : i ∉ hammingSupport x := by
      simp [hempty]
    exact hnot hi
  · intro hx
    rw [hx]
    exact HammingWeight_zero

theorem hammingSupport_add_subset_union {F : Type u} {ι : Type v}
    [AddGroup F] [DecidableEq F] [DecidableEq ι] [Fintype ι] (x y : Word F ι) :
    hammingSupport (x + y) ⊆ hammingSupport x ∪ hammingSupport y := by
  intro i hi
  simp [hammingSupport] at hi ⊢
  by_cases hx0 : x i = 0
  · right
    intro hy0
    exact hi (by simp [hx0, hy0])
  · left
    exact hx0

theorem HammingWeight_add_le {F : Type u} {ι : Type v}
    [AddGroup F] [DecidableEq F] [Fintype ι] (x y : Word F ι) :
    HammingWeight (x + y) ≤ HammingWeight x + HammingWeight y := by
  classical
  calc
    HammingWeight (x + y) = (hammingSupport (x + y)).card :=
      HammingWeight_eq_card_hammingSupport (x + y)
    _ ≤ (hammingSupport x ∪ hammingSupport y).card :=
      Finset.card_le_card (hammingSupport_add_subset_union x y)
    _ ≤ (hammingSupport x).card + (hammingSupport y).card :=
      Finset.card_union_le (hammingSupport x) (hammingSupport y)
    _ = HammingWeight x + HammingWeight y := by
      rw [← HammingWeight_eq_card_hammingSupport x, ← HammingWeight_eq_card_hammingSupport y]

/-- The block length of a finite-coordinate code. -/
def Length (_F : Type u) (ι : Type v) [Fintype ι] : Nat :=
  Fintype.card ι

/-- The ambient finite-coordinate word space has finrank equal to the code length. -/
@[simp]
theorem finrank_word_eq_length {F : Type u} {ι : Type v} [Field F] [Fintype ι] :
    Module.finrank F (Word F ι) = Length F ι := by
  rw [Length, Module.finrank_fintype_fun_eq_card]

/-- The dimension of a linear code as the finrank of its carrier submodule. -/
noncomputable def Dimension {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [Fintype ι] (C : LinearCode F ι) : Nat :=
  Module.finrank F C.carrier

/-- Unfolding lemma for the project code dimension. -/
@[simp]
theorem Dimension_eq_finrank_carrier {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [Fintype ι] (C : LinearCode F ι) :
    Dimension C = Module.finrank F C.carrier :=
  rfl

namespace LinearCode

variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

/-- A finite-coordinate linear code has dimension bounded by its ambient length. -/
theorem dimension_le_length (C : LinearCode F ι) :
    Dimension C ≤ Length F ι := by
  rw [Dimension_eq_finrank_carrier, ← finrank_word_eq_length]
  exact Submodule.finrank_le C.carrier

/--
The dual of a finite-coordinate linear code has dimension equal to ambient
length minus the dimension of the code.
-/
theorem dual_dimension_eq_length_sub_dimension (C : LinearCode F ι) :
    Dimension C.dual = Length F ι - Dimension C := by
  have hB : (LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))).Nondegenerate :=
    (wordPairing_nondegenerate (F := F) (ι := ι)).flip
  calc
    Dimension C.dual = Module.finrank F C.dual.carrier := rfl
    _ = Module.finrank F
          ((LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))).orthogonal
            C.carrier) := by
        rw [LinearCode.dual_carrier]
    _ = Module.finrank F (Word F ι) - Module.finrank F C.carrier := by
        exact LinearMap.BilinForm.finrank_orthogonal hB C.carrier
    _ = Length F ι - Dimension C := by
        rw [finrank_word_eq_length, Dimension_eq_finrank_carrier]

/-- Additive form of the code/dual dimension relationship. -/
theorem dimension_add_dual_dimension_eq_length (C : LinearCode F ι) :
    Dimension C + Dimension C.dual = Length F ι := by
  rw [dual_dimension_eq_length_sub_dimension]
  exact Nat.add_sub_of_le (dimension_le_length C)

end LinearCode

/-- A candidate minimum distance is the least nonzero Hamming weight in the code. -/
def MinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] (C : LinearCode F ι) (d : Nat) : Prop :=
  ∃ x : Word F ι,
    x ∈ C.carrier ∧ x ≠ 0 ∧ HammingWeight x = d ∧
      ∀ y : Word F ι, y ∈ C.carrier → y ≠ 0 → d ≤ HammingWeight y

/--
A candidate relative minimum distance is the least Hamming weight attained by
an ambient codeword outside the designated trivial subcode.
-/
def RelativeMinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (ambient trivial : LinearCode F ι) (d : Nat) : Prop :=
  ∃ x : Word F ι,
    x ∈ ambient.carrier ∧ x ∉ trivial.carrier ∧ HammingWeight x = d ∧
      ∀ y : Word F ι,
        y ∈ ambient.carrier → y ∉ trivial.carrier → d ≤ HammingWeight y

/-- The least weight of a pure-X logical representative in `zCode.dual \ xCode`. -/
def PureXLogicalMinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (xCode zCode : LinearCode F ι) (d : Nat) : Prop :=
  RelativeMinimumDistance zCode.dual xCode d

/-- The least weight of a pure-Z logical representative in `xCode.dual \ zCode`. -/
def PureZLogicalMinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (xCode zCode : LinearCode F ι) (d : Nat) : Prop :=
  RelativeMinimumDistance xCode.dual zCode d

/--
The least Hamming weight attained in the union of the nontrivial pure-X and
pure-Z logical representative sectors of a CSS pair.
-/
def AlgebraicCSSMinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (xCode zCode : LinearCode F ι) (d : Nat) : Prop :=
  ∃ x : Word F ι,
    ((x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
      (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)) ∧
    HammingWeight x = d ∧
      ∀ y : Word F ι,
        ((y ∈ zCode.dual.carrier ∧ y ∉ xCode.carrier) ∨
          (y ∈ xCode.dual.carrier ∧ y ∉ zCode.carrier)) →
        d ≤ HammingWeight y

/-- Any nonempty union of the two finite CSS logical sectors has an attained
algebraic minimum distance. -/
theorem exists_algebraicCSSMinimumDistance_of_exists_logical
    {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι]
    (xCode zCode : LinearCode F ι)
    (hne : ∃ x : Word F ι,
      (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
        (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)) :
    ∃ d : Nat, AlgebraicCSSMinimumDistance xCode zCode d := by
  classical
  let logicalWords : Finset (Word F ι) :=
    Finset.univ.filter fun x =>
      (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
        (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)
  have hnonempty : logicalWords.Nonempty := by
    rcases hne with ⟨x, hx⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image logicalWords
      (fun y : Word F ι => HammingWeight y) hnonempty
  have hxLogical :
      (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
        (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier) :=
    (Finset.mem_filter.mp hx).2
  refine ⟨HammingWeight x, x, hxLogical, rfl, ?_⟩
  intro y hy
  exact hmin y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)

/-- The minimum over both nontrivial CSS logical sectors is the minimum of their minima. -/
theorem algebraicCSSMinimumDistance_of_sector_minima
    {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {xCode zCode : LinearCode F ι} {dX dZ : Nat}
    (hX : PureXLogicalMinimumDistance xCode zCode dX)
    (hZ : PureZLogicalMinimumDistance xCode zCode dZ) :
    AlgebraicCSSMinimumDistance xCode zCode (min dX dZ) := by
  change RelativeMinimumDistance zCode.dual xCode dX at hX
  change RelativeMinimumDistance xCode.dual zCode dZ at hZ
  rcases hX with ⟨x, hxDual, hxTrivial, hxWeight, hxLeast⟩
  rcases hZ with ⟨z, hzDual, hzTrivial, hzWeight, hzLeast⟩
  unfold AlgebraicCSSMinimumDistance
  rcases le_total dX dZ with hXZ | hZX
  · refine ⟨x, Or.inl ⟨hxDual, hxTrivial⟩, ?_, ?_⟩
    · simpa [Nat.min_eq_left hXZ] using hxWeight
    · intro y hy
      rw [Nat.min_eq_left hXZ]
      rcases hy with hyX | hyZ
      · exact hxLeast y hyX.1 hyX.2
      · exact hXZ.trans (hzLeast y hyZ.1 hyZ.2)
  · refine ⟨z, Or.inr ⟨hzDual, hzTrivial⟩, ?_, ?_⟩
    · simpa [Nat.min_eq_right hZX] using hzWeight
    · intro y hy
      rw [Nat.min_eq_right hZX]
      rcases hy with hyX | hyZ
      · exact hZX.trans (hxLeast y hyX.1 hyX.2)
      · exact hzLeast y hyZ.1 hyZ.2

/--
No nonzero codeword has Hamming weight strictly below a proved minimum
distance.
-/
theorem not_mem_carrier_of_hammingWeight_lt_minimumDistance {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι] {C : LinearCode F ι} {d : Nat}
    (hmin : MinimumDistance C d) {x : Word F ι} (hx0 : x ≠ 0) (hlt : HammingWeight x < d) :
    x ∉ C.carrier := by
  intro hxC
  rcases hmin with ⟨_, _, _, _, hleast⟩
  exact (Nat.not_lt_of_ge (hleast x hxC hx0)) hlt

/-- A nonzero finite-coordinate linear code has a minimum distance. -/
theorem exists_minimumDistance_of_exists_nonzero {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι] (C : LinearCode F ι)
    (hC : ∃ x : Word F ι, x ∈ C.carrier ∧ x ≠ 0) :
    ∃ d : Nat, MinimumDistance C d := by
  classical
  let nonzeroCodewords : Finset (Word F ι) :=
    Finset.univ.filter fun x => x ∈ C.carrier ∧ x ≠ 0
  have hnonempty : nonzeroCodewords.Nonempty := by
    rcases hC with ⟨x, hxC, hx0⟩
    exact ⟨x, by simp [nonzeroCodewords, hxC, hx0]⟩
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image nonzeroCodewords (fun y : Word F ι => HammingWeight y) hnonempty
  have hxC : x ∈ C.carrier := by
    exact (Finset.mem_filter.mp hx).2.1
  have hx0 : x ≠ 0 := by
    exact (Finset.mem_filter.mp hx).2.2
  refine ⟨HammingWeight x, x, hxC, hx0, rfl, ?_⟩
  intro y hyC hy0
  exact hmin y (by simp [nonzeroCodewords, hyC, hy0])

/-- A nonempty relative sector of nested finite-coordinate codes has a minimum distance. -/
theorem exists_relativeMinimumDistance_of_exists_mem_not_mem
    {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (ambient trivial : LinearCode F ι) (_hsub : trivial.carrier ≤ ambient.carrier)
    (hne : ∃ x : Word F ι, x ∈ ambient.carrier ∧ x ∉ trivial.carrier) :
    ∃ d : Nat, RelativeMinimumDistance ambient trivial d := by
  classical
  let relativeCodewords : Finset (Word F ι) :=
    Finset.univ.filter fun x => x ∈ ambient.carrier ∧ x ∉ trivial.carrier
  have hnonempty : relativeCodewords.Nonempty := by
    rcases hne with ⟨x, hxAmbient, hxTrivial⟩
    exact ⟨x, by simp [relativeCodewords, hxAmbient, hxTrivial]⟩
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image relativeCodewords (fun y : Word F ι => HammingWeight y) hnonempty
  have hxAmbient : x ∈ ambient.carrier := by
    exact (Finset.mem_filter.mp hx).2.1
  have hxTrivial : x ∉ trivial.carrier := by
    exact (Finset.mem_filter.mp hx).2.2
  refine ⟨HammingWeight x, x, hxAmbient, hxTrivial, rfl, ?_⟩
  intro y hyAmbient hyTrivial
  exact hmin y (by simp [relativeCodewords, hyAmbient, hyTrivial])

/-- Length, dimension, and distance data for a finite-field linear code. -/
structure CodeParameters (F : Type u) (ι : Type v) [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] where
  code : LinearCode F ι
  length : Nat
  dimension : Nat
  minimumDistance : Nat
  length_eq : length = Length F ι
  dimension_eq : dimension = Dimension code
  distance_spec : MinimumDistance code minimumDistance

/-- The symplectic coordinate vector `(x, z)` used by Pauli representations. -/
structure SymplecticVector (F : Type u) (ι : Type v) [Field F] [Fintype F]
    [Fintype ι] where
  xPart : Word F ι
  zPart : Word F ι

/-- The standard finite-coordinate symplectic form. -/
def symplecticForm {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
    (a b : SymplecticVector F ι) : F :=
  Finset.sum Finset.univ (fun i : ι => a.xPart i * b.zPart i - a.zPart i * b.xPart i)

/-- The CSS X/Z symplectic pairing reduces to the finite-coordinate word pairing. -/
theorem symplecticForm_x_zero_zero_z_eq_wordPairing {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [Fintype ι] (x z : Word F ι) :
    symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        ({ xPart := 0, zPart := z } : SymplecticVector F ι) =
      wordPairing (F := F) (ι := ι) x z := by
  simp [symplecticForm, wordPairing_apply, dotProduct]

/-- Orthogonality to a set under the symplectic form. -/
def SymplecticOrthogonal {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [Fintype ι] (S : Set (SymplecticVector F ι)) (v : SymplecticVector F ι) :
    Prop :=
  ∀ w : SymplecticVector F ι, w ∈ S → symplecticForm v w = 0

namespace LinearCode

variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

/--
Codewords commute with words from the dual in the CSS X/Z symplectic shape used
by later stabilizer and CSS constructions.
-/
theorem symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual (C : LinearCode F ι)
    {x z : Word F ι} (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        ({ xPart := 0, zPart := z } : SymplecticVector F ι) = 0 := by
  rw [symplecticForm_x_zero_zero_z_eq_wordPairing]
  exact C.dual_orthogonal hx hz

end LinearCode

/-- A Pauli operator represented by a phase and symplectic coordinate data. -/
structure PauliSymplectic (F : Type u) (ι : Type v) [Field F] [Fintype F]
    [Fintype ι] where
  phase : F
  vector : SymplecticVector F ι

namespace PauliSymplectic

variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

/-- Two Pauli-symplectic representatives commute when their symplectic form vanishes. -/
def Commutes (P Q : PauliSymplectic F ι) : Prop :=
  symplecticForm P.vector Q.vector = 0

end PauliSymplectic

/-- A stabilizer code packages commuting Pauli-symplectic generators and a code subspace. -/
structure StabilizerCode (F : Type u) (ι : Type v) (H : Type w)
    [Field F] [Fintype F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H] where
  stabilizers : Set (PauliSymplectic F ι)
  code : Semantics.QuantumCode H
  isotropic : ∀ P : PauliSymplectic F ι, P ∈ stabilizers →
    ∀ Q : PauliSymplectic F ι, Q ∈ stabilizers → PauliSymplectic.Commutes P Q

/-- A CSS code surface built from X/Z linear codes and a stabilizer-code carrier. -/
structure CSSCode (F : Type u) (ι : Type v) (H : Type w)
    [Field F] [Fintype F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H] where
  xCode : LinearCode F ι
  zCode : LinearCode F ι
  stabilizer : StabilizerCode F ι H
  orthogonal : ∀ x : Word F ι, x ∈ xCode.carrier →
    ∀ z : Word F ι, z ∈ zCode.carrier →
      symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        ({ xPart := 0, zPart := z } : SymplecticVector F ι) = 0

/-- A three-term chain complex over a field. -/
structure ChainComplexData (F : Type u) (C0 C1 C2 : Type x) [Field F]
    [AddCommGroup C0] [Module F C0] [AddCommGroup C1] [Module F C1]
    [AddCommGroup C2] [Module F C2] where
  boundary1 : C1 →ₗ[F] C0
  boundary2 : C2 →ₗ[F] C1
  boundary_squared : boundary1.comp boundary2 = 0

namespace ChainComplexData

variable {F : Type u} {ι : Type v} {C0 C2 : Type (max u v)} [Field F] [Fintype F]
    [Fintype ι] [AddCommGroup C0] [Module F C0] [AddCommGroup C2] [Module F C2]

/--
The middle cycle code induced by the first boundary map when the middle chain
group is the finite-coordinate word space.
-/
def middleCycleCode (K : ChainComplexData F C0 (Word F ι) C2) : LinearCode F ι where
  carrier := LinearMap.ker K.boundary1

/--
The middle boundary code induced by the second boundary map when the middle
chain group is the finite-coordinate word space.
-/
def middleBoundaryCode (K : ChainComplexData F C0 (Word F ι) C2) : LinearCode F ι where
  carrier := LinearMap.range K.boundary2

/--
The finite-coordinate coboundary X-check code obtained as the range of the
transpose of the first boundary map.
-/
noncomputable def firstCoboundaryCheckCode {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) : LinearCode F ι where
  carrier := LinearMap.range (wordLinearMapTranspose K.boundary1)

@[simp]
theorem mem_middleCycleCode_iff (K : ChainComplexData F C0 (Word F ι) C2)
    (x : Word F ι) :
    x ∈ K.middleCycleCode.carrier ↔ K.boundary1 x = 0 := by
  rfl

@[simp]
theorem mem_middleBoundaryCode_iff (K : ChainComplexData F C0 (Word F ι) C2)
    (x : Word F ι) :
    x ∈ K.middleBoundaryCode.carrier ↔ ∃ y, K.boundary2 y = x := by
  rfl

@[simp]
theorem mem_firstCoboundaryCheckCode_iff {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) (x : Word F ι) :
    x ∈ K.firstCoboundaryCheckCode.carrier ↔
      ∃ y : Word F κ, wordLinearMapTranspose K.boundary1 y = x := by
  exact LinearMap.mem_range

/-- Boundaries are cycles for the middle finite-coordinate code induced by a chain complex. -/
theorem middleBoundaryCode_le_middleCycleCode
    (K : ChainComplexData F C0 (Word F ι) C2) :
    K.middleBoundaryCode.carrier ≤ K.middleCycleCode.carrier := by
  intro x hx
  rw [mem_middleCycleCode_iff]
  rcases (mem_middleBoundaryCode_iff K x).1 hx with ⟨y, hy⟩
  rw [← hy]
  change (K.boundary1.comp K.boundary2) y = 0
  rw [K.boundary_squared]
  rfl

/--
The middle-boundary submodule, viewed inside the middle-cycle submodule. This
is the actual boundary code pulled back along the cycle-code subtype.
-/
noncomputable def middleBoundaryInCycles
    (K : ChainComplexData F C0 (Word F ι) C2) :
    Submodule F K.middleCycleCode.carrier :=
  K.middleBoundaryCode.carrier.comap K.middleCycleCode.carrier.subtype

/--
The boundary-in-cycles submodule is linearly equivalent to the middle-boundary
code. The inclusion used here is proved from `boundary_squared`.
-/
noncomputable def middleBoundaryInCyclesEquiv
    (K : ChainComplexData F C0 (Word F ι) C2) :
    K.middleBoundaryInCycles ≃ₗ[F] K.middleBoundaryCode.carrier :=
  Submodule.comapSubtypeEquivOfLe K.middleBoundaryCode_le_middleCycleCode

/-- Middle homology as cycles modulo boundaries inside cycles. -/
noncomputable abbrev middleHomology
    (K : ChainComplexData F C0 (Word F ι) C2) :=
  K.middleCycleCode.carrier ⧸ K.middleBoundaryInCycles

@[simp]
theorem finrank_middleBoundaryInCycles_eq
    (K : ChainComplexData F C0 (Word F ι) C2) :
    Module.finrank F K.middleBoundaryInCycles = Dimension K.middleBoundaryCode := by
  rw [Dimension_eq_finrank_carrier]
  exact K.middleBoundaryInCyclesEquiv.finrank_eq

/--
The middle-homology dimension is the cycle dimension minus the boundary
dimension, computed as the quotient by the actual boundary submodule in cycles.
-/
theorem finrank_middleHomology_eq
    (K : ChainComplexData F C0 (Word F ι) C2) :
    Module.finrank F K.middleHomology =
      Dimension K.middleCycleCode - Dimension K.middleBoundaryCode := by
  have h := Submodule.finrank_quotient_add_finrank K.middleBoundaryInCycles
  rw [finrank_middleBoundaryInCycles_eq,
    ← Dimension_eq_finrank_carrier K.middleCycleCode] at h
  rw [← h]
  exact (Nat.add_sub_cancel_right _ _).symm

/--
The dual of the first coboundary check code is exactly the middle cycle code.
This is the finite-coordinate transpose/ker identity for the first boundary map.
-/
theorem firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) :
    K.firstCoboundaryCheckCode.dual.carrier = K.middleCycleCode.carrier := by
  ext x
  constructor
  · intro hx
    rw [mem_middleCycleCode_iff]
    have hpair : ∀ y : Word F κ, wordPairing (F := F) (ι := κ) y (K.boundary1 x) = 0 := by
      intro y
      have hmem : wordLinearMapTranspose K.boundary1 y ∈ K.firstCoboundaryCheckCode.carrier := by
        exact (mem_firstCoboundaryCheckCode_iff K (wordLinearMapTranspose K.boundary1 y)).2
          ⟨y, rfl⟩
      have hxpair := (LinearCode.mem_dual K.firstCoboundaryCheckCode x).1 hx
        (wordLinearMapTranspose K.boundary1 y) hmem
      rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply] at hxpair
      rw [wordPairing_wordLinearMapTranspose] at hxpair
      exact hxpair
    exact (wordPairing_nondegenerate (F := F) (ι := κ)).right (K.boundary1 x) hpair
  · intro hx
    refine (LinearCode.mem_dual K.firstCoboundaryCheckCode x).2 ?_
    intro c hc
    rcases (mem_firstCoboundaryCheckCode_iff K c).1 hc with ⟨y, rfl⟩
    rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply]
    rw [wordPairing_wordLinearMapTranspose]
    rw [(mem_middleCycleCode_iff K x).1 hx]
    simp

/--
For binary finite-coordinate chain-complex data, the CSS exponent obtained from
the coboundary and boundary check dimensions is the middle-homology dimension.
-/
theorem length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
    {ι κ lambda : Type u} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι)
      (Word (ZMod 2) lambda)) :
    Length (ZMod 2) ι
      - Dimension K.firstCoboundaryCheckCode
      - Dimension K.middleBoundaryCode =
    Module.finrank (ZMod 2) K.middleHomology := by
  have hcycle : Length (ZMod 2) ι - Dimension K.firstCoboundaryCheckCode =
      Dimension K.middleCycleCode := by
    calc
      Length (ZMod 2) ι - Dimension K.firstCoboundaryCheckCode =
          Dimension K.firstCoboundaryCheckCode.dual := by
        rw [LinearCode.dual_dimension_eq_length_sub_dimension]
      _ = Dimension K.middleCycleCode := by
        rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier]
        rw [firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode K]
  rw [hcycle, ← K.finrank_middleHomology_eq]

/--
Middle boundaries are orthogonal to the coboundary X-check code obtained from
the first boundary map.
-/
theorem middleBoundaryCode_le_firstCoboundaryCheckCode_dual {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) :
    K.middleBoundaryCode.carrier ≤ K.firstCoboundaryCheckCode.dual.carrier := by
  intro z hz
  refine (LinearCode.mem_dual K.firstCoboundaryCheckCode z).2 ?_
  intro x hx
  rcases (mem_middleBoundaryCode_iff K z).1 hz with ⟨c2, hc2⟩
  rcases (mem_firstCoboundaryCheckCode_iff K x).1 hx with ⟨y, hy⟩
  rw [← hy]
  rw [wordPairing_apply, dotProduct_comm]
  change wordPairing (F := F) (ι := ι) (wordLinearMapTranspose K.boundary1 y) z = 0
  rw [wordPairing_wordLinearMapTranspose]
  rw [← hc2]
  change wordPairing (F := F) (ι := κ) y ((K.boundary1.comp K.boundary2) c2) = 0
  rw [K.boundary_squared]
  simp

/--
The coboundary X-check code is symplectically orthogonal to the middle-boundary
Z-check code induced by the same chain-complex boundary maps.
-/
theorem firstCoboundaryCheckCode_orthogonal_middleBoundaryCode {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) :
    ∀ x : Word F ι, x ∈ K.firstCoboundaryCheckCode.carrier →
      ∀ z : Word F ι, z ∈ K.middleBoundaryCode.carrier →
        symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
          ({ xPart := 0, zPart := z } : SymplecticVector F ι) = 0 := by
  intro x hx z hz
  exact LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual
    K.firstCoboundaryCheckCode hx
    (K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual hz)

/-- The middle cocycle code is the kernel of the transpose of the second boundary map. -/
noncomputable def middleCocycleCode {lambda : Type v} [Fintype lambda]
    (K : ChainComplexData F C0 (Word F ι) (Word F lambda)) : LinearCode F ι where
  carrier := LinearMap.ker (wordLinearMapTranspose K.boundary2)

@[simp]
theorem mem_middleCocycleCode_iff {lambda : Type v} [Fintype lambda]
    (K : ChainComplexData F C0 (Word F ι) (Word F lambda)) (x : Word F ι) :
    x ∈ K.middleCocycleCode.carrier ↔ wordLinearMapTranspose K.boundary2 x = 0 := by
  rfl

/-- Orthogonality to every middle boundary is the cocycle equation `boundary2ᵀ x = 0`. -/
@[simp]
theorem mem_middleBoundaryCode_dual_iff {lambda : Type v} [Fintype lambda]
    (K : ChainComplexData F C0 (Word F ι) (Word F lambda)) (x : Word F ι) :
    x ∈ K.middleBoundaryCode.dual.carrier ↔
      wordLinearMapTranspose K.boundary2 x = 0 := by
  constructor
  · intro hx
    apply (wordPairing_nondegenerate (F := F) (ι := lambda)).left
    intro y
    rw [wordPairing_wordLinearMapTranspose]
    exact (LinearCode.mem_dual K.middleBoundaryCode x).1 hx
      (K.boundary2 y) ((K.mem_middleBoundaryCode_iff (K.boundary2 y)).2 ⟨y, rfl⟩)
  · intro hx
    refine (LinearCode.mem_dual K.middleBoundaryCode x).2 ?_
    intro c hc
    rcases (K.mem_middleBoundaryCode_iff c).1 hc with ⟨y, rfl⟩
    rw [← wordPairing_wordLinearMapTranspose K.boundary2 x y, hx]
    simp

/-- The dual of the middle-boundary code is exactly the middle cocycle code. -/
theorem middleBoundaryCode_dual_carrier_eq_middleCocycleCode {lambda : Type v}
    [Fintype lambda]
    (K : ChainComplexData F C0 (Word F ι) (Word F lambda)) :
    K.middleBoundaryCode.dual.carrier = K.middleCocycleCode.carrier := by
  ext x
  rw [K.mem_middleBoundaryCode_dual_iff, K.mem_middleCocycleCode_iff]

/-- The coboundary check code lies in the dual of the middle-boundary code. -/
theorem firstCoboundaryCheckCode_le_middleBoundaryCode_dual {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) :
    K.firstCoboundaryCheckCode.carrier ≤ K.middleBoundaryCode.dual.carrier :=
  LinearCode.le_dual_of_le_dual K.firstCoboundaryCheckCode K.middleBoundaryCode
    K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual

/-- The first coboundaries, viewed inside the directly defined middle cocycle code. -/
noncomputable def middleCoboundaryInCocycles {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    Submodule F K.middleCocycleCode.carrier :=
  K.firstCoboundaryCheckCode.carrier.comap K.middleCocycleCode.carrier.subtype

theorem firstCoboundaryCheckCode_le_middleCocycleCode {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.firstCoboundaryCheckCode.carrier ≤ K.middleCocycleCode.carrier := by
  rw [← K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
  exact K.firstCoboundaryCheckCode_le_middleBoundaryCode_dual

/-- The coboundaries-in-cocycles submodule is the actual first coboundary code. -/
noncomputable def middleCoboundaryInCocyclesEquiv {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.middleCoboundaryInCocycles ≃ₗ[F] K.firstCoboundaryCheckCode.carrier :=
  Submodule.comapSubtypeEquivOfLe K.firstCoboundaryCheckCode_le_middleCocycleCode

/-- Middle cohomology `H^1 = ker(boundary2ᵀ) / im(boundary1ᵀ)`. -/
noncomputable abbrev middleCohomology {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :=
  K.middleCocycleCode.carrier ⧸ K.middleCoboundaryInCocycles

/-- The first coboundary code, viewed inside the dual of the middle-boundary code. -/
noncomputable def firstCoboundaryInMiddleBoundaryDual {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    Submodule F K.middleBoundaryCode.dual.carrier :=
  K.firstCoboundaryCheckCode.carrier.comap K.middleBoundaryCode.dual.carrier.subtype

/-- The X-sector denominator is the full first coboundary code, not an intersection. -/
noncomputable def firstCoboundaryInMiddleBoundaryDualEquiv {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.firstCoboundaryInMiddleBoundaryDual ≃ₗ[F] K.firstCoboundaryCheckCode.carrier :=
  Submodule.comapSubtypeEquivOfLe K.firstCoboundaryCheckCode_le_middleBoundaryCode_dual

/-- The pure-X logical quotient `middleBoundaryCode.dual / firstCoboundaryCheckCode`. -/
noncomputable abbrev pureXLogicalQuotient {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :=
  K.middleBoundaryCode.dual.carrier ⧸ K.firstCoboundaryInMiddleBoundaryDual

/-- The middle-boundary code, viewed inside the dual of the first coboundary check code. -/
noncomputable def middleBoundaryInFirstCoboundaryDual {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    Submodule F K.firstCoboundaryCheckCode.dual.carrier :=
  K.middleBoundaryCode.carrier.comap K.firstCoboundaryCheckCode.dual.carrier.subtype

/-- The Z-sector denominator is the full middle-boundary code, not an intersection. -/
noncomputable def middleBoundaryInFirstCoboundaryDualEquiv {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.middleBoundaryInFirstCoboundaryDual ≃ₗ[F] K.middleBoundaryCode.carrier :=
  Submodule.comapSubtypeEquivOfLe K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual

/-- The pure-Z logical quotient `firstCoboundaryCheckCode.dual / middleBoundaryCode`. -/
noncomputable abbrev pureZLogicalQuotient {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :=
  K.firstCoboundaryCheckCode.dual.carrier ⧸ K.middleBoundaryInFirstCoboundaryDual

/-- The identity-on-words equivalence from boundary-dual representatives to cocycles. -/
noncomputable def middleBoundaryDualEquivMiddleCocycleCode {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.middleBoundaryCode.dual.carrier ≃ₗ[F] K.middleCocycleCode.carrier :=
  LinearEquiv.ofEq _ _ K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode

/-- The X-sector representative equivalence maps its denominator onto the `H^1` denominator. -/
theorem map_firstCoboundaryInMiddleBoundaryDual_eq_middleCoboundaryInCocycles
    {κ lambda : Type v} [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.firstCoboundaryInMiddleBoundaryDual.map
        K.middleBoundaryDualEquivMiddleCocycleCode.toLinearMap =
      K.middleCoboundaryInCocycles := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : Word F ι) ∈ K.firstCoboundaryCheckCode.carrier at hy
    change (K.middleBoundaryDualEquivMiddleCocycleCode y : Word F ι) ∈
      K.firstCoboundaryCheckCode.carrier
    simpa only [middleBoundaryDualEquivMiddleCocycleCode, LinearEquiv.coe_ofEq_apply] using hy
  · intro hx
    refine ⟨K.middleBoundaryDualEquivMiddleCocycleCode.symm x, ?_, ?_⟩
    · change (x : Word F ι) ∈ K.firstCoboundaryCheckCode.carrier at hx
      change (K.middleBoundaryDualEquivMiddleCocycleCode.symm x : Word F ι) ∈
        K.firstCoboundaryCheckCode.carrier
      simpa only [middleBoundaryDualEquivMiddleCocycleCode, LinearEquiv.ofEq_symm,
        LinearEquiv.coe_ofEq_apply] using hx
    · exact K.middleBoundaryDualEquivMiddleCocycleCode.apply_symm_apply x

/-- The pure-X logical quotient is explicitly linearly equivalent to middle cohomology. -/
noncomputable def pureXLogicalQuotientEquivMiddleCohomology {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.pureXLogicalQuotient ≃ₗ[F] K.middleCohomology :=
  Submodule.Quotient.equiv K.firstCoboundaryInMiddleBoundaryDual
    K.middleCoboundaryInCocycles K.middleBoundaryDualEquivMiddleCocycleCode
    K.map_firstCoboundaryInMiddleBoundaryDual_eq_middleCoboundaryInCocycles

@[simp]
theorem pureXLogicalQuotientEquivMiddleCohomology_mk {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda))
    (x : K.middleBoundaryCode.dual.carrier) :
    K.pureXLogicalQuotientEquivMiddleCohomology (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.middleBoundaryDualEquivMiddleCocycleCode x) := by
  rfl

/-- The identity-on-words equivalence from first-coboundary-dual representatives to cycles. -/
noncomputable def firstCoboundaryDualEquivMiddleCycleCode {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.firstCoboundaryCheckCode.dual.carrier ≃ₗ[F] K.middleCycleCode.carrier :=
  LinearEquiv.ofEq _ _ K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode

/-- The Z-sector representative equivalence maps its denominator onto the `H_1` denominator. -/
theorem map_middleBoundaryInFirstCoboundaryDual_eq_middleBoundaryInCycles
    {κ lambda : Type v} [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.middleBoundaryInFirstCoboundaryDual.map
        K.firstCoboundaryDualEquivMiddleCycleCode.toLinearMap =
      K.middleBoundaryInCycles := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : Word F ι) ∈ K.middleBoundaryCode.carrier at hy
    change (K.firstCoboundaryDualEquivMiddleCycleCode y : Word F ι) ∈
      K.middleBoundaryCode.carrier
    simpa only [firstCoboundaryDualEquivMiddleCycleCode, LinearEquiv.coe_ofEq_apply] using hy
  · intro hx
    refine ⟨K.firstCoboundaryDualEquivMiddleCycleCode.symm x, ?_, ?_⟩
    · change (x : Word F ι) ∈ K.middleBoundaryCode.carrier at hx
      change (K.firstCoboundaryDualEquivMiddleCycleCode.symm x : Word F ι) ∈
        K.middleBoundaryCode.carrier
      simpa only [firstCoboundaryDualEquivMiddleCycleCode, LinearEquiv.ofEq_symm,
        LinearEquiv.coe_ofEq_apply] using hx
    · exact K.firstCoboundaryDualEquivMiddleCycleCode.apply_symm_apply x

/-- The pure-Z logical quotient is explicitly linearly equivalent to existing middle homology. -/
noncomputable def pureZLogicalQuotientEquivMiddleHomology {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.pureZLogicalQuotient ≃ₗ[F] K.middleHomology :=
  Submodule.Quotient.equiv K.middleBoundaryInFirstCoboundaryDual K.middleBoundaryInCycles
    K.firstCoboundaryDualEquivMiddleCycleCode
    K.map_middleBoundaryInFirstCoboundaryDual_eq_middleBoundaryInCycles

@[simp]
theorem pureZLogicalQuotientEquivMiddleHomology_mk {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda))
    (x : K.firstCoboundaryCheckCode.dual.carrier) :
    K.pureZLogicalQuotientEquivMiddleHomology (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.firstCoboundaryDualEquivMiddleCycleCode x) := by
  rfl

end ChainComplexData

/-- A chain-complex code surface carrying homological data together with a CSS code. -/
structure ChainComplexCode (F : Type u) (ι : Type v) (H : Type w)
    (C0 C1 C2 : Type x) [Field F] [Fintype F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [AddCommGroup C0] [Module F C0] [AddCommGroup C1] [Module F C1]
    [AddCommGroup C2] [Module F C2] where
  complex : ChainComplexData F C0 C1 C2
  css : CSSCode F ι H
  cycles : LinearCode F ι
  boundaries : LinearCode F ι
  boundary_subset_cycles : ∀ word : Word F ι, word ∈ boundaries.carrier → word ∈ cycles.carrier

/-- Locality data used to record LDPC-style bounded checks and qubit incidence. -/
structure LocalityProfile where
  maxCheckWeight : Nat
  maxVariableDegree : Nat

/-- A locality profile is bounded when both check weight and variable degree fit the bound. -/
def BoundedLocality (profile : LocalityProfile) (bound : Nat) : Prop :=
  profile.maxCheckWeight ≤ bound ∧ profile.maxVariableDegree ≤ bound

/-- A QLDPC property surface for chain-complex codes with bounded locality data. -/
structure QLDPCProperty (F : Type u) (ι : Type v) (H : Type w)
    (C0 C1 C2 : Type x) [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [AddCommGroup C0] [Module F C0] [AddCommGroup C1] [Module F C1]
    [AddCommGroup C2] [Module F C2] where
  chainCode : ChainComplexCode F ι H C0 C1 C2
  parameters : CodeParameters F ι
  locality : LocalityProfile
  localityBound : Nat
  bounded_locality : BoundedLocality locality localityBound

/--
An algebraic-to-semantic bridge record for CSS data and M2 correctability predicates.

This packages the shared code carrier used by `CSSCode`, `KnillLaflammeCriterion`,
and `Correctable`; it does not assert a theorem relating the two predicates.
-/
structure SemanticAlgebraicBridge (F : Type u) (ι : Type v) (H K : Type w)
    [Field F] [Fintype F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K] where
  css : CSSCode F ι H
  errors : Set (Semantics.Operator H)
  noise : Semantics.QuantumChannel H K
  recovery : Semantics.QuantumChannel K H
  knill_laflamme : Semantics.KnillLaflammeCriterion H css.stabilizer.code errors
  correctable : Semantics.Correctable H K css.stabilizer.code noise recovery

end Coding
end QEC
