import QEC.Coding.FiniteAlternatingConstruction.LocalRegularity

/-!
# Constructive parity cleanup in finite grids and strips

The edges here join adjacent syndrome coordinates inside a single region.
Explicit paths produce a correction leaving only the region parity at any
chosen root. Embedding these edges into a replacement cylinder, and checking
their connecting-map support, are separate geometric obligations.
-/

namespace QEC.Coding.BDL26XLocalGridParity

open BDL26TannerLocalRegularity
open BDL26FiniteAlternatingCore

abbrev StripVertex (m : ℕ) := Fin m
abbrev StripEdge (m : ℕ) := Fin (m - 1)

def stripStart (m : ℕ) (e : StripEdge m) : StripVertex m :=
  ⟨e.val, by have := e.isLt; omega⟩

def stripEnd (m : ℕ) (e : StripEdge m) : StripVertex m :=
  ⟨e.val + 1, by have := e.isLt; omega⟩

/-- Traverse the first `k` edges of the strip, without choosing a path. -/
def stripPrefix (m : ℕ) (hm : 0 < m) :
    (k : ℕ) → (hk : k < m) →
      UndirectedPath (stripStart m) (stripEnd m) ⟨0, hm⟩ ⟨k, hk⟩
  | 0, _ => .nil
  | k + 1, hk => by
      exact .step (stripPrefix m hm k (by omega))
        ⟨k, by omega⟩ (Or.inl ⟨rfl, rfl⟩)

/-- An explicit adjacent-edge path between any two strip coordinates. -/
noncomputable def stripPath (m : ℕ) (hm : 0 < m)
    (root target : StripVertex m) :
    UndirectedPath (stripStart m) (stripEnd m) root target :=
  (stripPrefix m hm root.val root.isLt).reverse.append
    (stripPrefix m hm target.val target.isLt)

abbrev GridVertex (m : ℕ) := Fin m × Fin m
abbrev GridEdge (m : ℕ) :=
  (Fin (m - 1) × Fin m) ⊕ (Fin m × Fin (m - 1))

def gridStart (m : ℕ) : GridEdge m → GridVertex m
  | .inl e => (stripStart m e.1, e.2)
  | .inr e => (e.1, stripStart m e.2)

def gridEnd (m : ℕ) : GridEdge m → GridVertex m
  | .inl e => (stripEnd m e.1, e.2)
  | .inr e => (e.1, stripEnd m e.2)

/-- Move along one row and then one column using actual interior edges. -/
noncomputable def gridPath (m : ℕ) (hm : 0 < m)
    (root target : GridVertex m) :
    UndirectedPath (gridStart m) (gridEnd m) root target := by
  have row : UndirectedPath (gridStart m) (gridEnd m)
      root (target.1, root.2) :=
    UndirectedPath.map (edgeStart := stripStart m) (edgeEnd := stripEnd m)
      (edgeStart' := gridStart m) (edgeEnd' := gridEnd m) (fun i => (i, root.2))
      (fun i => Sum.inl (i, root.2)) (fun _ => rfl) (fun _ => rfl)
      (stripPath m hm root.1 target.1)
  have column : UndirectedPath (gridStart m) (gridEnd m)
      (target.1, root.2) target :=
    UndirectedPath.map (edgeStart := stripStart m) (edgeEnd := stripEnd m)
      (edgeStart' := gridStart m) (edgeEnd' := gridEnd m) (fun j => (target.1, j))
      (fun j => Sum.inr (target.1, j)) (fun _ => rfl) (fun _ => rfl)
      (stripPath m hm root.2 target.2)
  exact row.append column

/-- Strip cleanup uses only adjacent strip edges and retains its parity. -/
theorem strip_exists_boundary_eq_add_rootParity
    (m : ℕ) (hm : 0 < m) (root : StripVertex m)
    (syndrome : Word (ZMod 2) (StripVertex m)) :
    ∃ correction : Word (ZMod 2) (StripEdge m),
      graphBoundary (stripStart m) (stripEnd m) correction =
        syndrome + Pi.single root (totalParity syndrome) :=
  exists_graphBoundary_eq_add_rootParity
    (stripStart m) (stripEnd m) root (stripPath m hm root) syndrome

/-- Grid cleanup uses only adjacent grid edges and retains its parity. -/
theorem grid_exists_boundary_eq_add_rootParity
    (m : ℕ) (hm : 0 < m) (root : GridVertex m)
    (syndrome : Word (ZMod 2) (GridVertex m)) :
    ∃ correction : Word (ZMod 2) (GridEdge m),
      graphBoundary (gridStart m) (gridEnd m) correction =
        syndrome + Pi.single root (totalParity syndrome) :=
  exists_graphBoundary_eq_add_rootParity
    (gridStart m) (gridEnd m) root (gridPath m hm root) syndrome

end QEC.Coding.BDL26XLocalGridParity
