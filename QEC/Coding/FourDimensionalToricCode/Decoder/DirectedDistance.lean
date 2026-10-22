import QEC.Coding.FourDimensionalToricCode.Decoder.Multiscale

/-!
# Correctness of bounded directed-distance search

These internal API lemmas connect the executable search with its bounded
reachability predicate.  The final equivalence is restricted to radii within
the search budget; it does not use a separate simple-path theorem.
-/

namespace QEC.Coding.MultiscaleDecoder.DirectedGraph

universe v

variable {V : Type v} [Fintype V] [DecidableEq V]

/-- Increasing the path-length budget preserves reachability. -/
theorem reachableWithin_mono (G : DirectedGraph V) (u v : V)
    {m n : Nat} (hmn : m ≤ n) (h : G.reachableWithin m u v = true) :
    G.reachableWithin n u v = true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => simpa using h
  | succ k ih =>
      change (G.reachableWithin (m + k) u v ||
        decide (∃ w : V, G.edge u w = true ∧ G.reachableWithin (m + k) w v = true)) = true
      simp only [ih, Bool.true_or]

/-- A successful search returns a reachable length within its budget. -/
theorem distanceAux_some_spec (G : DirectedGraph V) (u v : V)
    {steps n : Nat} (h : G.distanceAux u v steps = some n) :
    n ≤ steps ∧ G.reachableWithin n u v = true := by
  induction steps generalizing n with
  | zero =>
      by_cases hr : G.reachableWithin 0 u v = true
      · have hn : 0 = n := by simpa [distanceAux, hr] using h
        subst n
        exact ⟨Nat.le_refl 0, hr⟩
      · simp [distanceAux, hr] at h
  | succ steps ih =>
      cases hp : G.distanceAux u v steps with
      | none =>
          by_cases hr : G.reachableWithin (steps + 1) u v = true
          · have hn : steps + 1 = n := by simpa [distanceAux, hp, hr] using h
            subst n
            exact ⟨Nat.le_refl _, hr⟩
          · simp [distanceAux, hp, hr] at h
      | some k =>
          have hn : k = n := by simpa [distanceAux, hp] using h
          subst n
          obtain ⟨hk, hr⟩ := ih hp
          exact ⟨Nat.le_trans hk (Nat.le_succ steps), hr⟩

/-- A reachable target makes the bounded search succeed. -/
theorem distanceAux_exists_of_reachableWithin (G : DirectedGraph V) (u v : V)
    (steps : Nat) (h : G.reachableWithin steps u v = true) :
    ∃ n, G.distanceAux u v steps = some n ∧ n ≤ steps := by
  cases steps with
  | zero => exact ⟨0, by simp [distanceAux, h], Nat.le_refl 0⟩
  | succ steps =>
      cases hp : G.distanceAux u v steps with
      | none => exact ⟨steps + 1, by simp [distanceAux, hp, h], Nat.le_refl _⟩
      | some n =>
          exact ⟨n, by simp [distanceAux, hp],
            Nat.le_trans (distanceAux_some_spec G u v hp).1 (Nat.le_succ steps)⟩

/-- Once a distance is found, extending the search keeps that result. -/
theorem distanceAux_some_mono (G : DirectedGraph V) (u v : V)
    {a b n : Nat} (hab : a ≤ b) (h : G.distanceAux u v a = some n) :
    G.distanceAux u v b = some n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction k with
  | zero => simpa using h
  | succ k ih =>
      change (match G.distanceAux u v (a + k) with
        | some value => some value
        | none => if G.reachableWithin (a + k + 1) u v then some (a + k + 1) else none) = some n
      rw [ih]

/-- The executable distance detects every radius within its finite budget. -/
theorem distance_le_iff_reachableWithin (G : DirectedGraph V) (u v : V)
    (r : Nat) (hr : r ≤ Fintype.card V) :
    G.distance u v ≤ (r : WithTop Nat) ↔ G.reachableWithin r u v = true := by
  cases hs : G.distanceAux u v (Fintype.card V) with
  | none =>
      constructor
      · intro h
        simp [distance, hs] at h
      · intro h
        obtain ⟨n, hn, _⟩ := distanceAux_exists_of_reachableWithin G u v r h
        have hc := distanceAux_some_mono G u v hr hn
        rw [hs] at hc
        cases hc
  | some n =>
      constructor
      · intro h
        have hnr : n ≤ r := by simpa [distance, hs] using h
        exact reachableWithin_mono G u v hnr (distanceAux_some_spec G u v hs).2
      · intro h
        obtain ⟨k, hk, hkr⟩ := distanceAux_exists_of_reachableWithin G u v r h
        have hc := distanceAux_some_mono G u v hr hk
        rw [hs] at hc
        have hnk : n = k := Option.some.inj hc
        simpa [distance, hs, hnk] using hkr

end QEC.Coding.MultiscaleDecoder.DirectedGraph
