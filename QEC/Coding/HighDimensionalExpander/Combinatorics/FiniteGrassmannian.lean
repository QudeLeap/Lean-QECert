import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Finite Grassmannian counts used by the local building

This file derives the finite-field counts needed for the colored links of
the `PGL₃` and `PGL₄` affine buildings.  In particular, the rank-two count
is proved by double-counting ordered independent frames; it is not supplied
as a numerical assumption.
 -/

noncomputable section

namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry

open Module

/-- The type of `r`-dimensional subspaces of a finite-dimensional vector
space. -/
def FiniteGrassmannian (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (r : ℕ) := {W : Submodule k V // Module.finrank k W = r}

instance (k V : Type*) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) : Finite (FiniteGrassmannian k V r) :=
  Finite.of_injective (fun W ↦ (W.1 : Set V))
    (fun _ _ h ↦ Subtype.ext (SetLike.coe_injective h))

/-- Ordered independent `r`-frames in `V`. -/
def IndependentFrames (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (r : ℕ) := {v : Fin r → V // LinearIndependent k v}

/-- Send an independent frame to the subspace that it spans. -/
noncomputable def frameSpanGrassmannian
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ) :
    IndependentFrames k V r → FiniteGrassmannian k V r :=
  fun v ↦ ⟨Submodule.span k (Set.range v.1), by
    rw [finrank_span_eq_card v.2, Fintype.card_fin]⟩

noncomputable def basisOfFrameFiber
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ)
    (W : FiniteGrassmannian k V r)
    (v : {v : IndependentFrames k V r // frameSpanGrassmannian k V r v = W}) :
    Basis (Fin r) k W.1 := by
  have hW : Submodule.span k (Set.range v.1.1) = W.1 :=
    congrArg Subtype.val v.property
  exact (Basis.span v.1.2).map (LinearEquiv.ofEq _ _ hW)

@[simp]
theorem coe_basisOfFrameFiber
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ)
    (W : FiniteGrassmannian k V r)
    (v : {v : IndependentFrames k V r // frameSpanGrassmannian k V r v = W})
    (i : Fin r) :
    ((basisOfFrameFiber k V r W v i : W.1) : V) = v.1.1 i := by
  unfold basisOfFrameFiber
  change ((Basis.span v.1.2) i : V) = v.1.1 i
  exact Basis.coe_span_apply v.1.2 i

/-- A basis of a fixed subspace is the same as an independent frame whose
span is that subspace. -/
noncomputable def grassmannianBasisEquivFrameFiber
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ)
    (W : FiniteGrassmannian k V r) :
    Basis (Fin r) k W.1 ≃
      {v : IndependentFrames k V r // frameSpanGrassmannian k V r v = W} where
  toFun b := ⟨⟨fun i ↦ (b i : V), b.linearIndependent.map' W.1.subtype
    (Submodule.ker_subtype _)⟩, by
      apply Subtype.ext
      change Submodule.span k (Set.range (W.1.subtype ∘ b)) = W.1
      rw [Set.range_comp, Submodule.span_image, b.span_eq,
        Submodule.map_subtype_top]⟩
  invFun v := basisOfFrameFiber k V r W v
  left_inv b := by
    apply DFunLike.coe_injective
    funext i
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp

instance finiteBasisFin
    (k V : Type*) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) : Finite (Basis (Fin r) k V) :=
  Finite.of_injective (fun b : Basis (Fin r) k V ↦ (b : Fin r → V))
    (fun _ _ h ↦ DFunLike.coe_injective h)

instance finiteIndependentFrames
    (k V : Type*) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) : Finite (IndependentFrames k V r) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable def basesEquivIndependentFrames
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (r : ℕ) (h : Module.finrank k V = r) :
    Basis (Fin r) k V ≃ IndependentFrames k V r where
  toFun b := ⟨b, b.linearIndependent⟩
  invFun v := basisOfLinearIndependentOfCardEqFinrank' v.1 v.2 (by simp [h])
  left_inv b := by ext i; simp
  right_inv v := by apply Subtype.ext; simp

theorem natCard_bases
    (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) (h : Module.finrank k V = r) :
    Nat.card (Basis (Fin r) k V) =
      ∏ i : Fin r, (Fintype.card k ^ r - Fintype.card k ^ i.val) := by
  rw [Nat.card_congr (basesEquivIndependentFrames k V r h)]
  simpa [h, IndependentFrames] using (card_linearIndependent (K := k) (V := V) h.ge)

/-- Double-count independent frames by the subspace that they span. -/
theorem natCard_finiteGrassmannian_mul
    (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) (hr : r ≤ Module.finrank k V) :
    Nat.card (FiniteGrassmannian k V r) *
        (∏ i : Fin r, (Fintype.card k ^ r - Fintype.card k ^ i.val)) =
      ∏ i : Fin r,
        (Fintype.card k ^ Module.finrank k V - Fintype.card k ^ i.val) := by
  classical
  letI : Fintype (FiniteGrassmannian k V r) := Fintype.ofFinite _
  have hb (W : FiniteGrassmannian k V r) :
      Nat.card (Basis (Fin r) k W.1) =
        ∏ i : Fin r, (Fintype.card k ^ r - Fintype.card k ^ i.val) :=
    natCard_bases k W.1 r W.property
  calc
    _ = Nat.card (Σ W : FiniteGrassmannian k V r,
        {v : IndependentFrames k V r // frameSpanGrassmannian k V r v = W}) := by
      rw [Nat.card_sigma]
      simp_rw [Nat.card_congr (grassmannianBasisEquivFrameFiber k V r _).symm, hb]
      simp
    _ = Nat.card (IndependentFrames k V r) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv (frameSpanGrassmannian k V r))
    _ = _ := card_linearIndependent hr

/-- The Gaussian-binomial count `[4 choose 2]_q`. -/
theorem natCard_rankTwoSubspaces_finFour
    (k : Type*) [Field k] [Fintype k] :
    Nat.card (FiniteGrassmannian k (Fin 4 → k) 2) =
      (Fintype.card k ^ 2 + 1) *
        (Fintype.card k ^ 2 + Fintype.card k + 1) := by
  let q := Fintype.card k
  change Nat.card (FiniteGrassmannian k (Fin 4 → k) 2) =
    (q ^ 2 + 1) * (q ^ 2 + q + 1)
  have h := natCard_finiteGrassmannian_mul k (Fin 4 → k) 2 (by simp)
  simp [Module.finrank_fintype_fun_eq_card] at h
  change Nat.card (FiniteGrassmannian k (Fin 4 → k) 2) *
      ((q ^ 2 - 1) * (q ^ 2 - q)) =
    (q ^ 4 - 1) * (q ^ 4 - q) at h
  have hq : 2 ≤ q := by
    apply Nat.succ_le_iff.mpr
    simpa only [q, Nat.card_eq_fintype_card] using
      (Finite.one_lt_card (α := k))
  have hq1 : 1 ≤ q := by omega
  have hp2one : 1 ≤ q ^ 2 := one_le_pow₀ hq1
  have hp4one : 1 ≤ q ^ 4 := one_le_pow₀ hq1
  have hqp2 : q ≤ q ^ 2 := by
    calc
      q = q * 1 := by simp
      _ ≤ q * q := Nat.mul_le_mul_left q hq1
      _ = q ^ 2 := by ring
  have hqp4 : q ≤ q ^ 4 := by
    calc
      q = q * 1 := by simp
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_left q (one_le_pow₀ hq1)
      _ = q ^ 4 := by ring
  have hqm : q - 1 + 1 = q := Nat.sub_add_cancel hq1
  have h21 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    nlinarith [Nat.sub_add_cancel hp2one, hqm]
  have h2q : q ^ 2 - q = q * (q - 1) := by
    nlinarith [Nat.sub_add_cancel hqp2, hqm]
  have h41 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    nlinarith [Nat.sub_add_cancel hp4one, Nat.sub_add_cancel hp2one]
  have h4q : q ^ 4 - q = q * (q - 1) * (q ^ 2 + q + 1) := by
    nlinarith [Nat.sub_add_cancel hqp4, hqm]
  have hfactor :
      ((q ^ 2 + 1) * (q ^ 2 + q + 1)) *
          ((q ^ 2 - 1) * (q ^ 2 - q)) =
        (q ^ 4 - 1) * (q ^ 4 - q) := by
    rw [h41, h4q, h21, h2q]
    ring
  have hden : 0 < (q ^ 2 - 1) * (q ^ 2 - q) := by
    exact Nat.mul_pos (Nat.sub_pos_of_lt (by nlinarith))
      (Nat.sub_pos_of_lt (by nlinarith))
  exact Nat.eq_of_mul_eq_mul_right hden (h.trans hfactor.symm)

theorem natCard_rankOneSubspaces_finThree
    (k : Type*) [Field k] [Fintype k] :
    Nat.card (FiniteGrassmannian k (Fin 3 → k) 1) =
      Fintype.card k ^ 2 + Fintype.card k + 1 := by
  let q := Fintype.card k
  have h := natCard_finiteGrassmannian_mul k (Fin 3 → k) 1 (by simp)
  simp [Module.finrank_fintype_fun_eq_card] at h
  change Nat.card (FiniteGrassmannian k (Fin 3 → k) 1) * (q - 1) =
    q ^ 3 - 1 at h
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using (Finite.one_lt_card (α := k))
  have hfactor : (q ^ 2 + q + 1) * (q - 1) = q ^ 3 - 1 := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using
      (geom_sum_mul_of_one_le hq.le 3)
  exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq) (h.trans hfactor.symm)

theorem natCard_rankTwoSubspaces_finThree
    (k : Type*) [Field k] [Fintype k] :
    Nat.card (FiniteGrassmannian k (Fin 3 → k) 2) =
      Fintype.card k ^ 2 + Fintype.card k + 1 := by
  let q := Fintype.card k
  have h := natCard_finiteGrassmannian_mul k (Fin 3 → k) 2 (by simp)
  simp [Module.finrank_fintype_fun_eq_card] at h
  change Nat.card (FiniteGrassmannian k (Fin 3 → k) 2) *
      ((q ^ 2 - 1) * (q ^ 2 - q)) =
    (q ^ 3 - 1) * (q ^ 3 - q) at h
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using (Finite.one_lt_card (α := k))
  have hq1 := hq.le
  have hp2one : 1 ≤ q ^ 2 := one_le_pow₀ hq1
  have hp3one : 1 ≤ q ^ 3 := one_le_pow₀ hq1
  have hqp2 : q ≤ q ^ 2 := by nlinarith
  have hqp3 : q ≤ q ^ 3 := by nlinarith
  have h21 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    nlinarith [Nat.sub_add_cancel hp2one, Nat.sub_add_cancel hq1]
  have h2q : q ^ 2 - q = q * (q - 1) := by
    nlinarith [Nat.sub_add_cancel hqp2, Nat.sub_add_cancel hq1]
  have h31 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    nlinarith [Nat.sub_add_cancel hp3one, Nat.sub_add_cancel hq1]
  have h3q : q ^ 3 - q = q * (q - 1) * (q + 1) := by
    nlinarith [Nat.sub_add_cancel hqp3, Nat.sub_add_cancel hq1]
  have hfactor : (q ^ 2 + q + 1) * ((q ^ 2 - 1) * (q ^ 2 - q)) =
      (q ^ 3 - 1) * (q ^ 3 - q) := by
    rw [h21, h2q, h31, h3q]
    ring
  have hden : 0 < (q ^ 2 - 1) * (q ^ 2 - q) :=
    Nat.mul_pos (Nat.sub_pos_of_lt (by nlinarith))
      (Nat.sub_pos_of_lt (by nlinarith))
  exact Nat.eq_of_mul_eq_mul_right hden (h.trans hfactor.symm)

theorem natCard_rankOneSubspaces_finFour
    (k : Type*) [Field k] [Fintype k] :
    Nat.card (FiniteGrassmannian k (Fin 4 → k) 1) =
      Fintype.card k ^ 3 + Fintype.card k ^ 2 + Fintype.card k + 1 := by
  let q := Fintype.card k
  have h := natCard_finiteGrassmannian_mul k (Fin 4 → k) 1 (by simp)
  simp [Module.finrank_fintype_fun_eq_card] at h
  change Nat.card (FiniteGrassmannian k (Fin 4 → k) 1) * (q - 1) =
    q ^ 4 - 1 at h
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using (Finite.one_lt_card (α := k))
  have hfactor : (q ^ 3 + q ^ 2 + q + 1) * (q - 1) = q ^ 4 - 1 := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using
      (geom_sum_mul_of_one_le hq.le 4)
  exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq) (h.trans hfactor.symm)

theorem natCard_rankThreeSubspaces_finFour
    (k : Type*) [Field k] [Fintype k] :
    Nat.card (FiniteGrassmannian k (Fin 4 → k) 3) =
      Fintype.card k ^ 3 + Fintype.card k ^ 2 + Fintype.card k + 1 := by
  let q := Fintype.card k
  have h := natCard_finiteGrassmannian_mul k (Fin 4 → k) 3 (by simp)
  simp [Module.finrank_fintype_fun_eq_card, Fin.prod_univ_succ] at h
  change Nat.card (FiniteGrassmannian k (Fin 4 → k) 3) *
      ((q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2))) =
    (q ^ 4 - 1) * ((q ^ 4 - q) * (q ^ 4 - q ^ 2)) at h
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using (Finite.one_lt_card (α := k))
  have hq1 := hq.le
  have h21 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc,
      mul_comm] using (geom_sum_mul_of_one_le hq1 2).symm
  have h31 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc,
      mul_comm] using (geom_sum_mul_of_one_le hq1 3).symm
  have h3q : q ^ 3 - q = q * (q - 1) * (q + 1) := by
    calc
      q ^ 3 - q = q * q ^ 2 - q * 1 := by congr 1 <;> ring
      _ = q * (q ^ 2 - 1) := (Nat.mul_sub_left_distrib q (q ^ 2) 1).symm
      _ = _ := by rw [h21]; ring
  have h3q2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    calc
      q ^ 3 - q ^ 2 = q ^ 2 * q - q ^ 2 * 1 := by congr 1 <;> ring
      _ = _ := (Nat.mul_sub_left_distrib (q ^ 2) q 1).symm
  have h41 : q ^ 4 - 1 = (q - 1) * (q ^ 3 + q ^ 2 + q + 1) := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc,
      mul_comm] using (geom_sum_mul_of_one_le hq1 4).symm
  have h4q : q ^ 4 - q = q * (q - 1) * (q ^ 2 + q + 1) := by
    calc
      q ^ 4 - q = q * q ^ 3 - q * 1 := by congr 1 <;> ring
      _ = q * (q ^ 3 - 1) := (Nat.mul_sub_left_distrib q (q ^ 3) 1).symm
      _ = _ := by rw [h31]; ring
  have h4q2 : q ^ 4 - q ^ 2 = q ^ 2 * (q - 1) * (q + 1) := by
    calc
      q ^ 4 - q ^ 2 = q ^ 2 * q ^ 2 - q ^ 2 * 1 := by congr 1 <;> ring
      _ = q ^ 2 * (q ^ 2 - 1) :=
        (Nat.mul_sub_left_distrib (q ^ 2) (q ^ 2) 1).symm
      _ = _ := by rw [h21]; ring
  have hfactor : (q ^ 3 + q ^ 2 + q + 1) *
      ((q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2))) =
    (q ^ 4 - 1) * ((q ^ 4 - q) * (q ^ 4 - q ^ 2)) := by
    rw [h31, h3q, h3q2, h41, h4q, h4q2]
    ring
  have hden : 0 < (q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2)) := by
    rw [h31, h3q, h3q2]
    have hqm : 0 < q - 1 := Nat.sub_pos_of_lt hq
    positivity
  exact Nat.eq_of_mul_eq_mul_right hden (h.trans hfactor.symm)

theorem natCard_projectiveSpace_finThree
    (k : Type*) [Field k] [Finite k] :
    Nat.card (Projectivization k (Fin 3 → k)) =
      Nat.card k ^ 2 + Nat.card k + 1 := by
  rw [Projectivization.card_of_finrank k (Fin 3 → k)
    (Module.finrank_fintype_fun_eq_card k)]
  norm_num [Finset.sum_range_succ]
  ring

theorem natCard_projectiveSpace_finFour
    (k : Type*) [Field k] [Finite k] :
    Nat.card (Projectivization k (Fin 4 → k)) =
      Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 := by
  rw [Projectivization.card_of_finrank k (Fin 4 → k)
    (Module.finrank_fintype_fun_eq_card k)]
  norm_num [Finset.sum_range_succ]
  ring

/-! ### Transitivity of the finite general linear group -/

/-- The first `r` standard coordinate vectors in `k^d`. -/
def coordinateFrame (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    Fin r → (Fin d → k) :=
  fun i ↦ Pi.single (Fin.castLE hr i) 1

theorem coordinateFrame_linearIndependent
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    LinearIndependent k (coordinateFrame k d r hr) := by
  exact (Pi.linearIndependent_single_one (Fin d) k).comp
    (Fin.castLEEmb hr) (Fin.castLEEmb hr).injective

/-- The standard coordinate `r`-plane in `k^d`. -/
def coordinateGrassmannian
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    FiniteGrassmannian k (Fin d → k) r :=
  frameSpanGrassmannian k (Fin d → k) r
    ⟨coordinateFrame k d r hr, coordinateFrame_linearIndependent k d r hr⟩

/-- Membership in the standard coordinate plane is exactly vanishing outside
the first `r` coordinates. -/
theorem mem_coordinateGrassmannian_iff
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (v : Fin d → k) :
    v ∈ (coordinateGrassmannian k d r hr).1 ↔
      ∀ i : Fin d, r ≤ i.val → v i = 0 := by
  constructor
  · intro hv
    change v ∈ Submodule.span k (Set.range (coordinateFrame k d r hr)) at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        intro i hi
        have hne : i ≠ Fin.castLE hr j := by
          intro h
          have : r ≤ j.val := by simpa [h] using hi
          exact (Nat.not_le_of_lt j.isLt) this
        simp [coordinateFrame, hne]
    | zero => simp
    | add x y _ _ hx hy =>
        intro i hi
        simp [hx i hi, hy i hi]
    | smul a x _ hx =>
        intro i hi
        simp [hx i hi]
  · intro hv
    change v ∈ Submodule.span k (Set.range (coordinateFrame k d r hr))
    have hsum : v = ∑ j : Fin r, v (Fin.castLE hr j) • coordinateFrame k d r hr j := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply]
      by_cases hi : i.val < r
      · let j : Fin r := ⟨i.val, hi⟩
        rw [show i = Fin.castLE hr j by apply Fin.ext; rfl]
        rw [Finset.sum_eq_single j]
        · simp [coordinateFrame]
        · intro b _ hb
          have hne : Fin.castLE hr j ≠ Fin.castLE hr b := by
            intro h
            apply hb
            exact Fin.castLE_injective hr h.symm
          simp [coordinateFrame, hne]
        · simp
      · have hzero : v i = 0 := hv i (Nat.le_of_not_gt hi)
        rw [hzero]
        symm
        apply Finset.sum_eq_zero
        intro j _
        have hne : i ≠ Fin.castLE hr j := by
          intro h
          have : i.val < r := by simpa [h] using j.isLt
          exact hi this
        simp [coordinateFrame, hne]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- A finite general-linear matrix stabilizes the standard coordinate plane
exactly when its lower-left block vanishes. -/
theorem map_coordinateGrassmannian_eq_self_iff
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) k) :
    (coordinateGrassmannian k d r hr).1.map
        (Matrix.GeneralLinearGroup.toLin g).val =
        (coordinateGrassmannian k d r hr).1 ↔
      ∀ i j : Fin d, r ≤ i.val → j.val < r → g i j = 0 := by
  let P := (coordinateGrassmannian k d r hr).1
  let e := Matrix.GeneralLinearGroup.toLin g
  constructor
  · intro hmap i j hi hj
    let j' : Fin r := ⟨j.val, hj⟩
    have hj_eq : Fin.castLE hr j' = j := by apply Fin.ext; rfl
    have hframe : coordinateFrame k d r hr j' ∈ P := by
      exact Submodule.subset_span ⟨j', rfl⟩
    change P.map e.val = P at hmap
    have himage : e.val (coordinateFrame k d r hr j') ∈ P.map e.val :=
      ⟨coordinateFrame k d r hr j', hframe, rfl⟩
    rw [hmap] at himage
    have hzero := (mem_coordinateGrassmannian_iff k d r hr _).mp himage i hi
    change Matrix.mulVec (g : Matrix (Fin d) (Fin d) k)
      (coordinateFrame k d r hr j') i = 0 at hzero
    simpa [coordinateFrame, Matrix.mulVec_single_one, hj_eq] using hzero
  · intro hblock
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      apply (mem_coordinateGrassmannian_iff k d r hr _).mpr
      intro i hi
      have hxzero := (mem_coordinateGrassmannian_iff k d r hr x).mp hx
      change ∑ j, g i j * x j = 0
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j.val < r
      · rw [hblock i j hi hj, zero_mul]
      · rw [hxzero j (Nat.le_of_not_gt hj), mul_zero]
    · change Module.finrank k
          (P.map (LinearMap.GeneralLinearGroup.toLinearEquiv e).toLinearMap) =
        Module.finrank k P
      exact LinearEquiv.finrank_map_eq
        (LinearMap.GeneralLinearGroup.toLinearEquiv e) P

/-- Two general-linear translates of a subspace agree exactly when their
relative matrix stabilizes that subspace. -/
theorem map_generalLinear_eq_map_iff
    (k : Type*) [Field k] (d : ℕ)
    (P : Submodule k (Fin d → k)) (a b : GL (Fin d) k) :
    P.map (Matrix.GeneralLinearGroup.toLin a).val =
        P.map (Matrix.GeneralLinearGroup.toLin b).val ↔
      P.map (Matrix.GeneralLinearGroup.toLin (a⁻¹ * b)).val = P := by
  have hcomp (x y : GL (Fin d) k) :
      (Matrix.GeneralLinearGroup.toLin x).val.comp
          (Matrix.GeneralLinearGroup.toLin y).val =
        (Matrix.GeneralLinearGroup.toLin (x * y)).val := by
    ext v i
    simp
  have hone : (Matrix.GeneralLinearGroup.toLin (1 : GL (Fin d) k)).val =
      LinearMap.id := by
    ext v i
    simp
  constructor
  · intro h
    have hc := congrArg
      (fun Q : Submodule k (Fin d → k) =>
        Q.map (Matrix.GeneralLinearGroup.toLin a⁻¹).val) h
    rw [← Submodule.map_comp, hcomp, ← Submodule.map_comp, hcomp] at hc
    have hia : a⁻¹ * a = 1 := by group
    rw [hia] at hc
    rw [hone, Submodule.map_id] at hc
    exact hc.symm
  · intro h
    have hc := congrArg
      (fun Q : Submodule k (Fin d → k) =>
        Q.map (Matrix.GeneralLinearGroup.toLin a).val) h
    rw [← Submodule.map_comp, hcomp] at hc
    have hab : a * (a⁻¹ * b) = b := by group
    rw [hab] at hc
    simpa using hc.symm

/-- Any `r`-plane is the image of the standard coordinate plane under an
actual linear automorphism. -/
theorem exists_linearEquiv_map_coordinateGrassmannian
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (W : FiniteGrassmannian k (Fin d → k) r) :
    ∃ g : (Fin d → k) ≃ₗ[k] (Fin d → k),
      (coordinateGrassmannian k d r hr).1.map g.toLinearMap = W.1 := by
  let P := (coordinateGrassmannian k d r hr).1
  let f : P ≃ₗ[k] W.1 := LinearEquiv.ofFinrankEq _ _ (by
    rw [show Module.finrank k P = r from (coordinateGrassmannian k d r hr).property,
      W.property])
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g y ∈ W.1
    rw [← hg ⟨y, hy⟩]
    exact (f ⟨y, hy⟩).property
  · intro hx
    let y : P := f.symm ⟨x, hx⟩
    refine ⟨y, y.property, ?_⟩
    change g (y : Fin d → k) = x
    rw [← hg y]
    simp [y]

/-- Matrix form of finite-Grassmannian transitivity. -/
theorem exists_generalLinear_map_coordinateGrassmannian
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (W : FiniteGrassmannian k (Fin d → k) r) :
    ∃ g : GL (Fin d) k,
      (coordinateGrassmannian k d r hr).1.map
          (Matrix.GeneralLinearGroup.toLin g).val = W.1 := by
  obtain ⟨e, he⟩ :=
    exists_linearEquiv_map_coordinateGrassmannian k d r hr W
  let g : GL (Fin d) k := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  refine ⟨g, ?_⟩
  simpa only [g, MulEquiv.apply_symm_apply,
    LinearMap.GeneralLinearGroup.ofLinearEquiv] using he

end QEC.Coding.HighDimensionalExpander.FiniteGeometry
