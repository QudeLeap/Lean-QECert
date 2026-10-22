import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.GridCover
import Mathlib.Tactic

/-! # Counted integer-to-real conversion for every actual grid center -/
namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- Integer literals are formed by unit real additions in the approved primitive model. -/
noncomputable def natRealQuery : ℕ → ℝ × ℕ
  | 0 => (0,1)
  | n+1 => let q := natRealQuery n
           (q.1+1,q.2+1)

theorem natRealQuery_value (n : ℕ) : (natRealQuery n).1 = (n : ℝ) := by
  induction n <;> simp_all [natRealQuery]

theorem natRealQuery_cost (n : ℕ) : (natRealQuery n).2 = n+1 := by
  induction n <;> simp_all [natRealQuery]

noncomputable def intRealQuery : ℤ → ℝ × ℕ
  | .ofNat n => natRealQuery n
  | .negSucc n => let q := natRealQuery (n+1)
                  (-q.1,q.2+1)

theorem intRealQuery_value (z : ℤ) : (intRealQuery z).1 = (z : ℝ) := by
  cases z <;> simp [intRealQuery,natRealQuery_value]

theorem intRealQuery_cost_le (z : ℤ) : (intRealQuery z).2 ≤ z.natAbs+2 := by
  cases z <;> simp [intRealQuery,natRealQuery_cost]

noncomputable def gridPointQuery (K : ℕ) (g : Grid K) : Space × ℕ :=
  let q0 := intRealQuery (g 0).val
  let q1 := intRealQuery (g 1).val
  let q2 := intRealQuery (g 2).val
  (WithLp.toLp 2 ![q0.1,q1.1,q2.1],q0.2+q1.2+q2.2+3)

theorem gridPointQuery_value (K : ℕ) (g : Grid K) : (gridPointQuery K g).1 = gridPoint K g := by
  ext j
  fin_cases j <;> simp [gridPointQuery,gridPoint,intRealQuery_value]

theorem gridCoordinate_abs_le (K : ℕ) (g : GridCoordinate K) : g.val.natAbs ≤ K := by
  have h := Finset.mem_Icc.mp g.property
  have hlo := h.1
  have hhi := h.2
  have ha : |g.val| ≤ (K : ℤ) := abs_le.mpr h
  have he : (g.val.natAbs : ℤ) = |g.val| := Int.natCast_natAbs g.val
  rw [← he] at ha
  exact_mod_cast ha

theorem gridPointQuery_cost_le (K : ℕ) (g : Grid K) : (gridPointQuery K g).2 ≤ 3*K+9 := by
  have h0 := (intRealQuery_cost_le (g 0).val).trans (Nat.add_le_add_right (gridCoordinate_abs_le K (g 0)) 2)
  have h1 := (intRealQuery_cost_le (g 1).val).trans (Nat.add_le_add_right (gridCoordinate_abs_le K (g 1)) 2)
  have h2 := (intRealQuery_cost_le (g 2).val).trans (Nat.add_le_add_right (gridCoordinate_abs_le K (g 2)) 2)
  dsimp only [gridPointQuery]
  omega

end QEC.Coding.BDL26RandomPerturbation
