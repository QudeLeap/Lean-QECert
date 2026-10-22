import QEC.Coding.Stabilizer.Cleaning
import QEC.Bounds.GeometricLocalityTradeoff.Model
/-!
# Alternating-strip cleaning and linear distance

This module formalizes the arithmetic and finite-strip route used in BT09's
linear-distance proposition.  It specializes the existing local stabilizer
Hamiltonian to a concrete two-dimensional finite lattice; it does not define a
second stabilizer-code or Hamiltonian interface.
-/

noncomputable section

namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian

open PauliSymplectic

/--
The arithmetic core of the BT09 alternating-strip construction: above the
source threshold, `L` is a sum of an even number of widths, each equal to
`r - 1` or `r`.
-/
theorem exists_even_strip_counts
    {L r : Nat} (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L) :
    ∃ a b : Nat, L = a * (r - 1) + b * r ∧ Even (a + b) := by
  let d := r - 1
  let q := L / d
  let s := L % d
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hdr : d + 1 = r := by
    dsimp [d]
    omega
  have hs : s < d := by
    exact Nat.mod_lt _ hdpos
  have hdecomp : L = q * d + s := by
    simpa [q, s, Nat.mul_comm] using (Nat.div_add_mod L d).symm
  have hq : 2 * d ≤ q := by
    apply (Nat.le_div_iff_mul_le hdpos).2
    dsimp [d] at *
    nlinarith
  by_cases hEven : Even q
  · refine ⟨q - s, s, ?_, ?_⟩
    · have hqs : q = q - s + s := by omega
      change L = (q - s) * d + s * r
      calc
        L = q * d + s := hdecomp
        _ = (q - s + s) * d + s := by rw [← hqs]
        _ = (q - s) * d + s * (d + 1) := by ring
        _ = (q - s) * d + s * r := by rw [hdr]
    · have hsum : q - s + s = q := by omega
      rw [hsum]
      exact hEven
  · have hOdd : Odd q := Nat.not_even_iff_odd.mp hEven
    refine ⟨q - s - r, s + (r - 1), ?_, ?_⟩
    · have hqsd : q = q - s - r + s + (d + 1) := by omega
      change L = (q - s - r) * d + (s + d) * r
      calc
        L = q * d + s := hdecomp
        _ = (q - s - r + s + (d + 1)) * d + s := by rw [← hqsd]
        _ = (q - s - r) * d + (s + d) * (d + 1) := by ring
        _ = (q - s - r) * d + (s + d) * r := by rw [hdr]
    · rcases hOdd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega

/--
A source-faithful width decomposition for the nondegenerate BT09 branch.
The individual widths, rather than an already separated strip family, are the
geometric data constructed by the arithmetic argument.
-/
structure AlternatingWidthDecomposition (L r : Nat) where
  widths : List Nat
  sum_widths : widths.sum = L
  even_length : Even widths.length
  width_eq : ∀ w ∈ widths, w = r - 1 ∨ w = r

/-- The concrete list containing the two width species from the BT09 proof. -/
def alternatingWidths (a b r : Nat) : List Nat :=
  List.replicate a (r - 1) ++ List.replicate b r

@[simp]
theorem length_alternatingWidths (a b r : Nat) :
    (alternatingWidths a b r).length = a + b := by
  simp [alternatingWidths]

@[simp]
theorem sum_alternatingWidths (a b r : Nat) :
    (alternatingWidths a b r).sum = a * (r - 1) + b * r := by
  simp [alternatingWidths]

theorem mem_alternatingWidths
    {a b r w : Nat} (hw : w ∈ alternatingWidths a b r) :
    w = r - 1 ∨ w = r := by
  simp [alternatingWidths] at hw
  rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/--
Above the exact BT09 threshold, the project constructs the alternating width
data internally.  The `r = 1` case is intentionally excluded here and handled
directly by the terminal geometric proposition.
-/
theorem exists_alternatingWidthDecomposition
    {L r : Nat} (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L) :
    Nonempty (AlternatingWidthDecomposition L r) := by
  obtain ⟨a, b, hab, heven⟩ := exists_even_strip_counts hr hL
  exact
    ⟨{
      widths := alternatingWidths a b r
      sum_widths := by simpa using hab.symm
      even_length := by simpa using heven
      width_eq := by
        intro w hw
        exact mem_alternatingWidths hw
    }⟩

namespace StripGeometry

/-- The concrete two-dimensional square site type reused by the BT09 route. -/
abbrev Site (L : Nat) := Fin L × Fin L

/-- An open-boundary interval of columns, lifted to a full-height strip. -/
def openVerticalInterval (L start width : Nat) : Finset (Site L) :=
  Finset.univ.filter fun p => start ≤ p.1.val ∧ p.1.val < start + width

@[simp]
theorem mem_openVerticalInterval_iff
    {L start width : Nat} (p : Site L) :
    p ∈ openVerticalInterval L start width ↔
      start ≤ p.1.val ∧ p.1.val < start + width := by
  simp [openVerticalInterval]

/-- A periodic interval of columns, lifted to a full-height strip. -/
def periodicVerticalInterval (L start width : Nat) : Finset (Site L) :=
  let s := start % L
  Finset.univ.filter fun p =>
    (s ≤ p.1.val ∧ p.1.val < s + width) ∨
      p.1.val + L < s + width

@[simp]
theorem mem_periodicVerticalInterval_iff
    {L start width : Nat} (p : Site L) :
    p ∈ periodicVerticalInterval L start width ↔
      ((start % L ≤ p.1.val ∧ p.1.val < start % L + width) ∨
        p.1.val + L < start % L + width) := by
  simp [periodicVerticalInterval]

/--
Two regions are separated at open-boundary range `r` when no actual open
interval of width at most `r` meets both.
-/
def OpenIntervalSeparated
    (L r : Nat) (A B : Finset (Site L)) : Prop :=
  ∀ start width, width ≤ r →
    Disjoint (openVerticalInterval L start width) A ∨
      Disjoint (openVerticalInterval L start width) B

/--
Two regions are separated at periodic range `r` when no actual cyclic interval
of width at most `r` meets both.
-/
def PeriodicIntervalSeparated
    (L r : Nat) (A B : Finset (Site L)) : Prop :=
  ∀ start width, width ≤ r →
    Disjoint (periodicVerticalInterval L start width) A ∨
      Disjoint (periodicVerticalInterval L start width) B

/-- Coordinate gap sufficient for open-interval separation. -/
def OpenSeparatedByGap
    {L : Nat} (r : Nat) (A B : Finset (Site L)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ B, p.1.val + r ≤ q.1.val

/--
The two directed coordinate gaps sufficient for cyclic separation, with `A`
lying before `B` in the chosen cut of the circle.
-/
def PeriodicSeparatedByGaps
    (L r : Nat) (A B : Finset (Site L)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ B,
    p.1.val + r ≤ q.1.val ∧ r + q.1.val ≤ L + p.1.val

theorem openIntervalSeparated_of_gap
    {L r : Nat} {A B : Finset (Site L)}
    (hgap : OpenSeparatedByGap r A B) :
    OpenIntervalSeparated L r A B := by
  intro start width hwidth
  by_cases hA :
      Disjoint (openVerticalInterval L start width) A
  · exact Or.inl hA
  · right
    apply Finset.disjoint_left.mpr
    intro q hqInterval hqB
    rcases Finset.not_disjoint_iff.mp hA with
      ⟨p, hpInterval, hpA⟩
    have hpBounds :=
      (mem_openVerticalInterval_iff p).1 hpInterval
    have hqBounds :=
      (mem_openVerticalInterval_iff q).1 hqInterval
    have hpq := hgap p hpA q hqB
    omega

theorem periodicIntervalSeparated_of_gaps
    {L r : Nat} {A B : Finset (Site L)}
    (hgap : PeriodicSeparatedByGaps L r A B) :
    PeriodicIntervalSeparated L r A B := by
  intro start width hwidth
  by_cases hA :
      Disjoint (periodicVerticalInterval L start width) A
  · exact Or.inl hA
  · right
    apply Finset.disjoint_left.mpr
    intro q hqInterval hqB
    rcases Finset.not_disjoint_iff.mp hA with
      ⟨p, hpInterval, hpA⟩
    have hpBounds :=
      (mem_periodicVerticalInterval_iff p).1 hpInterval
    have hqBounds :=
      (mem_periodicVerticalInterval_iff q).1 hqInterval
    have hpq := hgap p hpA q hqB
    have hLpos : 0 < L := by omega
    have hstart : start % L < L := Nat.mod_lt start hLpos
    rcases hpBounds with hpDirect | hpWrap <;>
      rcases hqBounds with hqDirect | hqWrap <;> omega

/-- Consecutive open-boundary strips generated by a width list. -/
def openStripListAux (L start : Nat) : List Nat → List (Finset (Site L))
  | [] => []
  | width :: widths =>
      openVerticalInterval L start width ::
        openStripListAux L (start + width) widths

/-- The strips in positions `0, 2, 4, ...`. -/
def firstParity {α : Type*} : List α → List α
  | [] => []
  | [A] => [A]
  | A :: _ :: regions => A :: firstParity regions

/-- The strips in positions `1, 3, 5, ...`. -/
def secondParity {α : Type*} : List α → List α
  | [] => []
  | [_] => []
  | _ :: B :: regions => B :: secondParity regions

@[simp]
theorem firstParity_nil {α : Type*} :
    firstParity ([] : List α) = [] := rfl

@[simp]
theorem firstParity_singleton {α : Type*} (A : α) :
    firstParity [A] = [A] := rfl

@[simp]
theorem firstParity_cons_cons {α : Type*}
    (A B : α) (regions : List α) :
    firstParity (A :: B :: regions) = A :: firstParity regions := rfl

@[simp]
theorem secondParity_nil {α : Type*} :
    secondParity ([] : List α) = [] := rfl

@[simp]
theorem secondParity_singleton {α : Type*} (A : α) :
    secondParity [A] = [] := rfl

@[simp]
theorem secondParity_cons_cons {α : Type*}
    (A B : α) (regions : List α) :
    secondParity (A :: B :: regions) = B :: secondParity regions := rfl

theorem secondParity_cons_eq_firstParity {α : Type*} :
    ∀ (A : α) (regions : List α),
      secondParity (A :: regions) = firstParity regions
  | _, [] => rfl
  | _, [_] => rfl
  | _, B :: C :: regions =>
      congrArg (B :: ·)
        (secondParity_cons_eq_firstParity C regions)

theorem firstParity_sublist {α : Type*} :
    ∀ regions : List α, List.Sublist (firstParity regions) regions
  | [] => .slnil
  | [A] => .cons_cons A .slnil
  | A :: B :: regions =>
      .cons_cons A (.cons B (firstParity_sublist regions))

theorem secondParity_sublist {α : Type*} :
    ∀ regions : List α, List.Sublist (secondParity regions) regions
  | [] => .slnil
  | [A] => .cons A .slnil
  | A :: B :: regions =>
      .cons A (.cons_cons B (secondParity_sublist regions))

theorem firstParity_pairwise
    {α : Type*} {relation : α → α → Prop} {regions : List α}
    (h : regions.Pairwise relation) :
    (firstParity regions).Pairwise relation :=
  h.sublist (firstParity_sublist regions)

theorem secondParity_pairwise
    {α : Type*} {relation : α → α → Prop} {regions : List α}
    (h : regions.Pairwise relation) :
    (secondParity regions).Pairwise relation :=
  h.sublist (secondParity_sublist regions)

/-- Every site in a generated strip lies weakly to the right of its start. -/
theorem mem_openStripListAux_lower
    {L start : Nat} {widths : List Nat}
    {R : Finset (Site L)} (hR : R ∈ openStripListAux L start widths)
    {p : Site L} (hp : p ∈ R) :
    start ≤ p.1.val := by
  induction widths generalizing start R with
  | nil => simp [openStripListAux] at hR
  | cons width widths ih =>
      simp only [openStripListAux, List.mem_cons] at hR
      rcases hR with rfl | hR
      · exact (mem_openVerticalInterval_iff p).1 hp |>.1
      · exact (Nat.le_add_right start width).trans
          (ih (start := start + width) hR hp)

/-- Every constructed strip remembers one of the supplied widths. -/
theorem mem_openStripListAux_exists
    {L start : Nat} {widths : List Nat}
    {R : Finset (Site L)} (hR : R ∈ openStripListAux L start widths) :
    ∃ stripStart width, width ∈ widths ∧
      R = openVerticalInterval L stripStart width := by
  induction widths generalizing start R with
  | nil => simp [openStripListAux] at hR
  | cons width widths ih =>
      simp only [openStripListAux, List.mem_cons] at hR
      rcases hR with rfl | hR
      · exact ⟨start, width, by simp, rfl⟩
      · obtain ⟨stripStart, tailWidth, htail, rfl⟩ :=
          ih (start := start + width) hR
        exact ⟨stripStart, tailWidth, by simp [htail], rfl⟩

/-- Consecutive strips are pairwise disjoint. -/
theorem openStripListAux_pairwise_disjoint
    (L start : Nat) (widths : List Nat) :
    (openStripListAux L start widths).Pairwise Disjoint := by
  induction widths generalizing start with
  | nil => simp [openStripListAux]
  | cons width widths ih =>
      rw [openStripListAux, List.pairwise_cons]
      constructor
      · intro R hR
        apply Finset.disjoint_left.mpr
        intro p hpHead hpR
        have hpUpper :=
          (mem_openVerticalInterval_iff p).1 hpHead |>.2
        have hpLower :=
          mem_openStripListAux_lower
            (start := start + width) hR hpR
        omega
      · exact ih (start + width)

/-- Distinct consecutive positive-width strips have at least the unit gap. -/
theorem openStripListAux_pairwise_unitGap
    (L start : Nat) (widths : List Nat)
    (hPositive : ∀ width ∈ widths, 1 ≤ width) :
    (openStripListAux L start widths).Pairwise
      (OpenSeparatedByGap 1) := by
  induction widths generalizing start with
  | nil => simp [openStripListAux]
  | cons width widths ih =>
      rw [openStripListAux, List.pairwise_cons]
      constructor
      · intro R hR p hp q hq
        have hpUpper :=
          (mem_openVerticalInterval_iff p).1 hp |>.2
        have hqLower :=
          mem_openStripListAux_lower
            (start := start + width) hR hq
        omega
      · exact ih (start + width)
          (by
            intro tailWidth htail
            exact hPositive tailWidth (by simp [htail]))

/-- Unit-gap strip lists are separated from open intervals of width one. -/
theorem openStripListAux_pairwise_openUnitSeparated
    (L start : Nat) (widths : List Nat)
    (hPositive : ∀ width ∈ widths, 1 ≤ width) :
    (openStripListAux L start widths).Pairwise
      (OpenIntervalSeparated L 1) :=
  (openStripListAux_pairwise_unitGap
    L start widths hPositive).imp openIntervalSeparated_of_gap

/-- Unit-gap strip lists are also separated from cyclic width-one intervals. -/
theorem openStripListAux_pairwise_periodicUnitSeparated
    (L : Nat) (widths : List Nat)
    (hPositive : ∀ width ∈ widths, 1 ≤ width) :
    (openStripListAux L 0 widths).Pairwise
      (PeriodicIntervalSeparated L 1) := by
  have hDirect :=
    openStripListAux_pairwise_unitGap L 0 widths hPositive
  apply hDirect.imp
  intro A B hAB
  apply periodicIntervalSeparated_of_gaps
  intro p hp q hq
  constructor
  · exact hAB p hp q hq
  · have hqUpper : q.1.val < L := q.1.isLt
    omega

/-- Every two first-parity strips have the required directed coordinate gap. -/
theorem firstParity_pairwise_openSeparatedByGap
    (L r start : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (firstParity (openStripListAux L start widths)).Pairwise
      (OpenSeparatedByGap r) := by
  induction widths using List.twoStepInduction generalizing start with
  | nil =>
      simp [openStripListAux]
  | singleton width =>
      simp [openStripListAux]
  | cons_cons width₀ width₁ widths ih _ =>
      simp only [openStripListAux, firstParity_cons_cons,
        List.pairwise_cons]
      constructor
      · intro R hR p hp q hq
        have hpUpper :=
          (mem_openVerticalInterval_iff p).1 hp |>.2
        have hRAll :
            R ∈ openStripListAux L
              ((start + width₀) + width₁) widths :=
          (firstParity_sublist _).subset hR
        have hqLower :=
          mem_openStripListAux_lower hRAll hq
        have hwidth₁ : r - 1 ≤ width₁ :=
          hLower width₁ (by simp)
        omega
      · apply ih (start := (start + width₀) + width₁)
        intro width hwidth
        exact hLower width (by simp [hwidth])

/--
Every two first-parity strips are separated from open intervals of range `r`
when each intervening strip has width at least `r - 1`.
-/
theorem firstParity_open_pairwise_intervalSeparated
    (L r start : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (firstParity (openStripListAux L start widths)).Pairwise
      (OpenIntervalSeparated L r) :=
  (firstParity_pairwise_openSeparatedByGap
    L r start widths hLower).imp openIntervalSeparated_of_gap

/-- The directed coordinate-gap form for the second parity. -/
theorem secondParity_pairwise_openSeparatedByGap
    (L r start : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (secondParity (openStripListAux L start widths)).Pairwise
      (OpenSeparatedByGap r) := by
  cases widths with
  | nil => simp [openStripListAux]
  | cons width widths =>
      rw [openStripListAux, secondParity_cons_eq_firstParity]
      apply firstParity_pairwise_openSeparatedByGap
      intro w hw
      exact hLower w (by simp [hw])

/-- The same open-interval separation for the second parity. -/
theorem secondParity_open_pairwise_intervalSeparated
    (L r start : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (secondParity (openStripListAux L start widths)).Pairwise
      (OpenIntervalSeparated L r) := by
  cases widths with
  | nil => simp [openStripListAux]
  | cons width widths =>
      rw [openStripListAux, secondParity_cons_eq_firstParity]
      exact
        (firstParity_pairwise_openSeparatedByGap
          L r (start + width) widths
          (by
            intro w hw
            exact hLower w (by simp [hw]))).imp
          openIntervalSeparated_of_gap

/--
A first-parity strip always has a following second-parity strip, so its sites
remain one interaction range before the end of an even-width decomposition.
-/
theorem firstParity_site_add_range_le_end
    (L r start : Nat) (widths : List Nat)
    (hEven : Even widths.length)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width)
    {R : Finset (Site L)}
    (hR : R ∈ firstParity (openStripListAux L start widths))
    {p : Site L} (hp : p ∈ R) :
    p.1.val + r ≤ start + widths.sum := by
  induction widths using List.twoStepInduction generalizing start R with
  | nil =>
      simp [openStripListAux] at hR
  | singleton width =>
      rcases hEven with ⟨k, hk⟩
      simp at hk
      omega
  | cons_cons width₀ width₁ widths ih _ =>
      simp only [openStripListAux, firstParity_cons_cons,
        List.mem_cons] at hR
      rcases hR with rfl | hR
      · have hpUpper :=
          (mem_openVerticalInterval_iff p).1 hp |>.2
        have hwidth₁ : r - 1 ≤ width₁ :=
          hLower width₁ (by simp)
        simp only [List.sum_cons]
        omega
      · have hEvenTail : Even widths.length := by
          rcases hEven with ⟨k, hk⟩
          refine ⟨k - 1, ?_⟩
          simp only [List.length_cons] at hk
          omega
        have hTail :=
          ih (start := (start + width₀) + width₁)
            hEvenTail
            (by
              intro width hwidth
              exact hLower width (by simp [hwidth]))
            hR hp
        simpa [List.sum_cons, Nat.add_assoc] using hTail

/-- Every second-parity site lies after the first strip. -/
theorem secondParity_site_lower
    {L start : Nat} {width₀ : Nat} {widths : List Nat}
    {R : Finset (Site L)}
    (hR :
      R ∈ secondParity
        (openStripListAux L start (width₀ :: widths)))
    {p : Site L} (hp : p ∈ R) :
    start + width₀ ≤ p.1.val := by
  rw [openStripListAux, secondParity_cons_eq_firstParity] at hR
  have hRAll :
      R ∈ openStripListAux L (start + width₀) widths :=
    (firstParity_sublist _).subset hR
  exact mem_openStripListAux_lower hRAll hp

/-- Periodic separation for the first parity, including the seam gap. -/
theorem firstParity_periodic_pairwise_intervalSeparated
    (L r : Nat) (widths : List Nat)
    (hSum : widths.sum = L)
    (hEven : Even widths.length)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (firstParity (openStripListAux L 0 widths)).Pairwise
      (PeriodicIntervalSeparated L r) := by
  let regions := firstParity (openStripListAux L 0 widths)
  have hDirect :
      regions.Pairwise (OpenSeparatedByGap r) :=
    firstParity_pairwise_openSeparatedByGap L r 0 widths hLower
  apply hDirect.imp_of_mem
  intro A B hA hB hAB
  apply periodicIntervalSeparated_of_gaps
  intro p hp q hq
  constructor
  · exact hAB p hp q hq
  · have hqEnd :=
      firstParity_site_add_range_le_end
        L r 0 widths hEven hLower hB hq
    omega

/-- Periodic separation for the second parity, including the seam gap. -/
theorem secondParity_periodic_pairwise_intervalSeparated
    (L r : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (secondParity (openStripListAux L 0 widths)).Pairwise
      (PeriodicIntervalSeparated L r) := by
  have hDirect :=
    secondParity_pairwise_openSeparatedByGap L r 0 widths hLower
  apply hDirect.imp_of_mem
  intro A B hA _ hAB
  apply periodicIntervalSeparated_of_gaps
  intro p hp q hq
  constructor
  · exact hAB p hp q hq
  · cases widths with
    | nil => simp [openStripListAux] at hA
    | cons width₀ widths =>
        have hpLower :=
          secondParity_site_lower
            (start := 0) (width₀ := width₀) hA hp
        have hwidth₀ : r - 1 ≤ width₀ :=
          hLower width₀ (by simp)
        have hqUpper : q.1.val < L := q.1.isLt
        omega

/-- Actual open-interval support locality for every selected generator. -/
def HasOpenIntervalGeneratorSupport
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (r : Nat) : Prop :=
  ∀ j, ∃ start width, width ≤ r ∧
    support (H.generators j) ⊆ openVerticalInterval L start width

/-- Actual cyclic-interval support locality for every selected generator. -/
def HasPeriodicIntervalGeneratorSupport
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (r : Nat) : Prop :=
  ∀ j, ∃ start width, width ≤ r ∧
    support (H.generators j) ⊆ periodicVerticalInterval L start width

end StripGeometry

/-- No selected Hamiltonian generator has actual support in both regions. -/
def NoSharedGenerator
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R T : Finset ι) : Prop :=
  ∀ j, ¬ (H.GeneratorMeets R j ∧ H.GeneratorMeets T j)

theorem noSharedGenerator_of_openIntervalSeparated
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (r : Nat) (A B : Finset (StripGeometry.Site L))
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (hSeparated : StripGeometry.OpenIntervalSeparated L r A B) :
    H.NoSharedGenerator A B := by
  intro j hboth
  obtain ⟨start, width, hwidth, hsupport⟩ := hLocal j
  rcases hSeparated start width hwidth with hA | hB
  · exact hboth.1
      (Finset.disjoint_of_subset_left hsupport hA)
  · exact hboth.2
      (Finset.disjoint_of_subset_left hsupport hB)

theorem noSharedGenerator_of_periodicIntervalSeparated
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (r : Nat) (A B : Finset (StripGeometry.Site L))
    (hLocal : StripGeometry.HasPeriodicIntervalGeneratorSupport H r)
    (hSeparated : StripGeometry.PeriodicIntervalSeparated L r A B) :
    H.NoSharedGenerator A B := by
  intro j hboth
  obtain ⟨start, width, hwidth, hsupport⟩ := hLocal j
  rcases hSeparated start width hwidth with hA | hB
  · exact hboth.1
      (Finset.disjoint_of_subset_left hsupport hA)
  · exact hboth.2
      (Finset.disjoint_of_subset_left hsupport hB)

theorem noSharedGenerator_symm
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    {R T : Finset ι} (h : H.NoSharedGenerator R T) :
    H.NoSharedGenerator T R := by
  intro j hboth
  exact h j ⟨hboth.2, hboth.1⟩

/-- Pairwise generator separation relates any two distinct list members. -/
theorem noSharedGenerator_of_pairwise_mem
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    {regions : List (Finset ι)}
    (hpairwise : regions.Pairwise H.NoSharedGenerator)
    {R T : Finset ι} (hR : R ∈ regions) (hT : T ∈ regions)
    (hRT : R ≠ T) :
    H.NoSharedGenerator R T := by
  induction regions generalizing R T with
  | nil => simp at hR
  | cons A regions ih =>
      rw [List.pairwise_cons] at hpairwise
      simp only [List.mem_cons] at hR hT
      rcases hR with rfl | hR
      · rcases hT with rfl | hT
        · exact (hRT rfl).elim
        · exact hpairwise.1 T hT
      · rcases hT with rfl | hT
        · exact H.noSharedGenerator_symm (hpairwise.1 R hR)
        · exact ih (R := R) (T := T) hpairwise.2 hR hT hRT

/-- The finite union of a list of physical regions. -/
def regionUnion {ι : Type*} [DecidableEq ι] : List (Finset ι) → Finset ι
  | [] => ∅
  | R :: regions => R ∪ regionUnion regions

@[simp]
theorem mem_regionUnion_iff
    {ι : Type*} [DecidableEq ι] (i : ι) (regions : List (Finset ι)) :
    i ∈ regionUnion regions ↔ ∃ R ∈ regions, i ∈ R := by
  induction regions with
  | nil => simp [regionUnion]
  | cons R regions ih =>
      simp [regionUnion, ih]

namespace StripGeometry

/-- Consecutive strips combine to the single interval of their total width. -/
theorem regionUnion_openStripListAux
    (L start : Nat) (widths : List Nat) :
    regionUnion (openStripListAux L start widths) =
      openVerticalInterval L start widths.sum := by
  induction widths generalizing start with
  | nil =>
      ext p
      simp [openStripListAux, regionUnion]
  | cons width widths ih =>
      rw [openStripListAux, regionUnion, ih]
      ext p
      simp only [Finset.mem_union, mem_openVerticalInterval_iff,
        List.sum_cons]
      constructor
      · intro hp
        rcases hp with hp | hp <;> omega
      · intro hp
        by_cases hleft : p.1.val < start + width
        · exact Or.inl ⟨hp.1, hleft⟩
        · exact Or.inr ⟨by omega, by simpa [Nat.add_assoc] using hp.2⟩

/-- A width decomposition summing to `L` covers the full square lattice. -/
theorem regionUnion_openStrips_eq_univ
    {L r : Nat} (D : AlternatingWidthDecomposition L r) :
    regionUnion (openStripListAux L 0 D.widths) =
      (Finset.univ : Finset (Site L)) := by
  rw [regionUnion_openStripListAux, D.sum_widths]
  ext p
  simp

/-- A full-height strip of width `width` has at most `width * L` sites. -/
theorem card_openVerticalInterval_le
    (L start width : Nat) :
    (openVerticalInterval L start width).card ≤ width * L := by
  let f :
      {p // p ∈ openVerticalInterval L start width} →
        Fin width × Fin L :=
    fun p =>
      (⟨p.1.1.val - start, by
          have hp := (mem_openVerticalInterval_iff p.1).1 p.2
          omega⟩,
        p.1.2)
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hpBounds :=
        (mem_openVerticalInterval_iff p.1).1 p.2
      have hqBounds :=
        (mem_openVerticalInterval_iff q.1).1 q.2
      have hx :
          p.1.1.val - start = q.1.1.val - start :=
        congrArg (fun z => z.1.val) hpq
      omega
    · exact
        congrArg (fun z : Fin width × Fin L => z.2) hpq
  have hcard :=
    Fintype.card_le_of_injective f hf
  rw [← Fintype.card_coe (openVerticalInterval L start width)]
  simpa only [Fintype.card_prod, Fintype.card_fin] using hcard

/-- The two parity sublists together have the same union as the full list. -/
theorem regionUnion_firstParity_union_secondParity
    {α : Type*} [DecidableEq α] (regions : List (Finset α)) :
    regionUnion (firstParity regions) ∪
        regionUnion (secondParity regions) =
      regionUnion regions := by
  induction regions using List.twoStepInduction with
  | nil => simp [regionUnion]
  | singleton R => simp [regionUnion]
  | cons_cons R T regions ih _ =>
      simp only [firstParity_cons_cons, secondParity_cons_cons,
        regionUnion]
      ext x
      have ihx :
          (x ∈ regionUnion (firstParity regions) ∨
              x ∈ regionUnion (secondParity regions)) ↔
            x ∈ regionUnion regions := by
        simpa using Finset.ext_iff.mp ih x
      simp only [Finset.mem_union]
      tauto

end StripGeometry

/--
A product generated by checks meeting `R` is disjoint from `T` when no selected
check meets both regions.
-/
theorem disjoint_support_of_generatedByMeeting_of_noSharedGenerator
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R T : Finset ι) (S : Binary ι)
    (hseparated : H.NoSharedGenerator R T)
    (hS : H.GeneratedByMeeting R S) :
    Disjoint (support S) T := by
  induction hS with
  | one =>
      simp
  | generator j =>
      by_contra hnot
      have hmeetT : H.GeneratorMeets T j.1 := by
        simpa [GeneratorMeets, generatorSupport] using hnot
      exact hseparated j.1 ⟨j.2, hmeetT⟩
  | mul _ _ ihP ihQ =>
      apply Finset.disjoint_left.mpr
      intro i hi hiT
      rcases Finset.mem_union.mp (support_binaryMul_subset _ _ hi) with hiP | hiQ
      · exact (Finset.disjoint_left.mp ihP hiP hiT)
      · exact (Finset.disjoint_left.mp ihQ hiQ hiT)
  | dagger _ ihP =>
      simpa using ihP

/-- Pairwise generator separation from a head region extends to the tail union. -/
theorem noSharedGenerator_regionUnion
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (regions : List (Finset ι))
    (hseparated : ∀ T ∈ regions, H.NoSharedGenerator R T) :
    H.NoSharedGenerator R (regionUnion regions) := by
  intro j hboth
  rcases Finset.not_disjoint_iff.mp hboth.2 with ⟨i, hiGenerator, hiUnion⟩
  rcases (mem_regionUnion_iff i regions).1 hiUnion with ⟨T, hT, hiT⟩
  apply hseparated T hT j
  refine ⟨hboth.1, ?_⟩
  exact Finset.not_disjoint_iff.mpr ⟨i, hiGenerator, hiT⟩

/-- Commuting with every selected generator implies membership in the existing normalizer. -/
theorem inBinaryNormalizer_of_commutes_selectedGenerators
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (hcommutes : ∀ j, Commutes E (H.generators j)) :
    H.code.1.InBinaryNormalizer E := by
  intro G hG
  rw [← H.generated_eq] at hG
  induction hG with
  | one => exact commutes_binaryOne_right E
  | generator j => exact hcommutes j
  | mul _ _ ihP ihQ => exact commutes_binaryMul_right ihP ihQ
  | dagger _ ihP => exact commutes_binaryDagger_right ihP

/--
If no selected generator meets both sides of a disjoint two-region cover, a
normalizer Pauli restricts to a normalizer Pauli on each side.
-/
theorem inBinaryNormalizer_restrictBinaryTo_of_noSharedGenerator
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (A B : Finset ι) (E : Binary ι)
    (hdisjoint : Disjoint A B)
    (hseparated : H.NoSharedGenerator A B)
    (hsupport : support E ⊆ A ∪ B)
    (hE : H.code.1.InBinaryNormalizer E) :
    H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo A E) ∧
      H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo B E) := by
  have hdecompose :=
    Locality.restrictBinaryTo_vector_add_of_support_subset_union
      A B E hdisjoint hsupport
  have hside :
      ∀ (R T : Finset ι), Disjoint R T →
        H.NoSharedGenerator R T →
        E.vector =
          (Locality.restrictBinaryTo R E).vector +
            (Locality.restrictBinaryTo T E).vector →
        H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo R E) := by
    intro R T hRT hsep hdecomposeRT
    apply H.inBinaryNormalizer_of_commutes_selectedGenerators
    intro j
    by_cases hRG : Disjoint R (support (H.generators j))
    · exact Locality.commutes_of_disjoint_support _ _
        (Finset.disjoint_of_subset_left
          (Locality.support_restrictBinaryTo_subset R E) hRG)
    · have hTG : Disjoint T (support (H.generators j)) := by
        by_contra hnotTG
        apply hsep j
        constructor
        · show ¬ Disjoint (support (H.generators j)) R
          exact fun h => hRG h.symm
        · show ¬ Disjoint (support (H.generators j)) T
          exact fun h => hnotTG h.symm
      have hcommT :
          Commutes (Locality.restrictBinaryTo T E) (H.generators j) :=
        Locality.commutes_of_disjoint_support _ _
          (Finset.disjoint_of_subset_left
            (Locality.support_restrictBinaryTo_subset T E) hTG)
      have hcommE : Commutes E (H.generators j) :=
        hE (H.generators j) (H.generator_mem_generatedGroup j)
      change symplecticForm E.vector (H.generators j).vector = 0 at hcommE
      change symplecticForm (Locality.restrictBinaryTo T E).vector
          (H.generators j).vector = 0 at hcommT
      change symplecticForm (Locality.restrictBinaryTo R E).vector
          (H.generators j).vector = 0
      rw [hdecomposeRT, Locality.symplecticForm_add_left, hcommT] at hcommE
      simpa using hcommE
  refine ⟨hside A B hdisjoint hseparated hdecompose, ?_⟩
  exact hside B A hdisjoint.symm (H.noSharedGenerator_symm hseparated)
    (hdecompose.trans (add_comm _ _))

/-- Restricting to a smaller region after a larger one preserves the smaller vector. -/
theorem restrictBinaryTo_restrictBinaryTo_vector_of_subset_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R S : Finset ι) (hRS : R ⊆ S) (E : Binary ι) :
    (Locality.restrictBinaryTo R (Locality.restrictBinaryTo S E)).vector =
      (Locality.restrictBinaryTo R E).vector := by
  apply (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
  apply Prod.ext <;> funext i
  · by_cases hi : i ∈ R
    · have hiS := hRS hi
      simp [Locality.restrictBinaryTo, hi, hiS, SymplecticVector.toProdEquiv]
    · simp [Locality.restrictBinaryTo, hi, SymplecticVector.toProdEquiv]
  · by_cases hi : i ∈ R
    · have hiS := hRS hi
      simp [Locality.restrictBinaryTo, hi, hiS, SymplecticVector.toProdEquiv]
    · simp [Locality.restrictBinaryTo, hi, SymplecticVector.toProdEquiv]

/-- A strong list-level pairwise relation, convenient for selecting arbitrary members. -/
def RegionsPairwise
    {α : Type*} (relation : α → α → Prop) (regions : List α) : Prop :=
  ∀ R ∈ regions, ∀ T ∈ regions, R ≠ T → relation R T

/-- Pairwise-disjoint finite regions are disjoint from the union of the remaining tail. -/
theorem disjoint_regionUnion_of_cons
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (regions : List (Finset ι))
    (hpairwise : (R :: regions).Pairwise Disjoint) :
    Disjoint R (regionUnion regions) := by
  apply Finset.disjoint_left.mpr
  intro i hiR hiUnion
  rcases (mem_regionUnion_iff i regions).1 hiUnion with ⟨T, hT, hiT⟩
  exact Finset.disjoint_left.mp
    ((List.pairwise_cons.mp hpairwise).1 T hT) hiR hiT

/-- Sum of the phase-free Pauli restriction vectors over a finite region list. -/
def restrictionVectorSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (regions : List (Finset ι)) (E : Binary ι) :
    SymplecticVector (ZMod 2) ι :=
  (regions.map fun R => (Locality.restrictBinaryTo R E).vector).sum

/-- A Pauli supported on pairwise-disjoint regions is the sum of its restrictions. -/
theorem vector_eq_restrictionVectorSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (regions : List (Finset ι))
    (hpairwise : regions.Pairwise Disjoint)
    (E : Binary ι) (hsupport : support E ⊆ regionUnion regions) :
    E.vector = restrictionVectorSum regions E := by
  induction regions generalizing E with
  | nil =>
      have hdecompose :=
        Locality.restrictBinaryTo_vector_add_of_support_subset_union
          (∅ : Finset ι) ∅ E (by simp) (by simpa [regionUnion] using hsupport)
      have hzero : (Locality.restrictBinaryTo (∅ : Finset ι) E).vector = 0 := by
        simp only [Locality.restrictBinaryTo, Finset.notMem_empty, if_false]
        rfl
      rw [hzero, zero_add] at hdecompose
      simpa only [restrictionVectorSum, List.map_nil, List.sum_nil] using hdecompose
  | cons R regions ih =>
      have hpairTail : regions.Pairwise Disjoint := hpairwise.tail
      have hdisjoint : Disjoint R (regionUnion regions) :=
        disjoint_regionUnion_of_cons R regions hpairwise
      have hdecompose :=
        Locality.restrictBinaryTo_vector_add_of_support_subset_union
          R (regionUnion regions) E hdisjoint
          (by simpa [regionUnion] using hsupport)
      let outsideR := Locality.restrictBinaryTo (regionUnion regions) E
      have hOutsideSupport : support outsideR ⊆ regionUnion regions :=
        Locality.support_restrictBinaryTo_subset _ _
      have ihOutside :
          outsideR.vector = restrictionVectorSum regions outsideR :=
        ih hpairTail outsideR hOutsideSupport
      have hrestrict :
          ∀ T ∈ regions,
            (Locality.restrictBinaryTo T outsideR).vector =
              (Locality.restrictBinaryTo T E).vector := by
        intro T hT
        apply restrictBinaryTo_restrictBinaryTo_vector_of_subset_left
        intro i hiT
        exact (mem_regionUnion_iff i regions).2 ⟨T, hT, hiT⟩
      have hmap :
          restrictionVectorSum regions outsideR =
            restrictionVectorSum regions E := by
        unfold restrictionVectorSum
        congr 1
        apply List.map_congr_left
        exact hrestrict
      calc
        E.vector =
            (Locality.restrictBinaryTo R E).vector + outsideR.vector := by
              simpa [outsideR] using hdecompose
        _ = (Locality.restrictBinaryTo R E).vector +
              restrictionVectorSum regions outsideR := by rw [ihOutside]
        _ = (Locality.restrictBinaryTo R E).vector +
              restrictionVectorSum regions E := by rw [hmap]
        _ = restrictionVectorSum (R :: regions) E := by
              simp [restrictionVectorSum]

/--
If all restrictions of a Pauli to a disjoint supporting partition are generated
up to sign, then the original Pauli is generated up to sign.
-/
theorem inGeneratedGroupUpToSign_of_restrictions
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hpairwise : regions.Pairwise Disjoint)
    (E : Binary ι) (hsupport : support E ⊆ regionUnion regions)
    (hgenerated :
      ∀ R ∈ regions,
        H.code.1.InGeneratedGroupUpToSign (Locality.restrictBinaryTo R E)) :
    H.code.1.InGeneratedGroupUpToSign E := by
  have hsumMem :
      restrictionVectorSum regions E ∈
        H.code.1.generatedVectorSubspace := by
    unfold restrictionVectorSum
    clear hpairwise hsupport
    induction regions with
    | nil =>
        simp
    | cons R regions ih =>
        rw [List.map_cons, List.sum_cons]
        apply Submodule.add_mem
        · exact
            (H.code.1.vector_mem_generatedVectorSubspace_iff
              (Locality.restrictBinaryTo R E)).2
              (hgenerated R (by simp))
        · apply ih
          intro T hT
          exact hgenerated T (by simp [hT])
  apply (H.code.1.vector_mem_generatedVectorSubspace_iff E).1
  rw [vector_eq_restrictionVectorSum regions hpairwise E hsupport]
  exact hsumMem

/-- A member of a generator-separated covering partition inherits normalizer membership. -/
theorem inBinaryNormalizer_restrictBinaryTo_of_mem
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hseparated : regions.Pairwise H.NoSharedGenerator)
    (E : Binary ι) (hsupport : support E ⊆ regionUnion regions)
    (hE : H.code.1.InBinaryNormalizer E)
    (R : Finset ι) (hR : R ∈ regions) :
    H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo R E) := by
  let outsideR := regionUnion regions \ R
  have hdisjoint : Disjoint R outsideR := by
    apply Finset.disjoint_left.mpr
    intro i hiR hiOutside
    exact (Finset.mem_sdiff.mp hiOutside).2 hiR
  have hcover : support E ⊆ R ∪ outsideR := by
    intro i hiE
    have hiUnion := hsupport hiE
    by_cases hiR : i ∈ R
    · exact Finset.mem_union_left _ hiR
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hiUnion, hiR⟩)
  have hNoShared : H.NoSharedGenerator R outsideR := by
    intro j hboth
    rcases Finset.not_disjoint_iff.mp hboth.2 with
      ⟨i, hiGenerator, hiOutside⟩
    have hiUnion : i ∈ regionUnion regions :=
      (Finset.mem_sdiff.mp hiOutside).1
    have hiNotR : i ∉ R :=
      (Finset.mem_sdiff.mp hiOutside).2
    rcases (mem_regionUnion_iff i regions).1 hiUnion with ⟨T, hT, hiT⟩
    have hTR : T ≠ R := by
      intro hEq
      subst T
      exact hiNotR hiT
    have hTRSeparated : H.NoSharedGenerator T R :=
      H.noSharedGenerator_of_pairwise_mem
        (regions := regions) (R := T) (T := R)
        hseparated hT hR hTR
    exact (H.noSharedGenerator_symm hTRSeparated j)
      ⟨hboth.1, Finset.not_disjoint_iff.mpr ⟨i, hiGenerator, hiT⟩⟩
  exact
    (H.inBinaryNormalizer_restrictBinaryTo_of_noSharedGenerator
      R outsideR E hdisjoint hNoShared hcover hE).1

/--
A nontrivial logical Pauli supported on a disjoint, generator-separated finite
partition has a nontrivial logical restriction on at least one member.
-/
theorem exists_nontrivial_logical_restriction
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hdisjoint : regions.Pairwise Disjoint)
    (hseparated : regions.Pairwise H.NoSharedGenerator)
    (E : Binary ι)
    (hNormalizer : H.code.1.InBinaryNormalizer E)
    (hNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign E)
    (hsupport : support E ⊆ regionUnion regions) :
    ∃ R ∈ regions,
      H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo R E) ∧
      ¬ H.code.1.InGeneratedGroupUpToSign (Locality.restrictBinaryTo R E) ∧
      support (Locality.restrictBinaryTo R E) ⊆ R := by
  by_contra hnone
  push Not at hnone
  have hgenerated :
      ∀ R ∈ regions,
        H.code.1.InGeneratedGroupUpToSign (Locality.restrictBinaryTo R E) := by
    intro R hR
    have hRNormalizer :=
      H.inBinaryNormalizer_restrictBinaryTo_of_mem
        regions hseparated E hsupport hNormalizer R hR
    by_contra hRNontrivial
    exact hnone R hR hRNormalizer hRNontrivial
      (Locality.support_restrictBinaryTo_subset R E)
  exact hNontrivial
    (H.inGeneratedGroupUpToSign_of_restrictions
      regions hdisjoint E hsupport hgenerated)

/-- A region contains no nontrivial logical Pauli representative. -/
def NoLocalLogical
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) : Prop :=
  ¬ ∃ P : Binary ι,
      H.code.1.InBinaryNormalizer P ∧
      ¬ H.code.1.InGeneratedGroupUpToSign P ∧
      support P ⊆ R

/--
Repeated BT09 cleaning for a pairwise generator-separated list of regions.
The returned correction is an actual member of the existing generated group.
-/
theorem exists_cleanedOutside_regionUnion
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hpairwise : regions.Pairwise H.NoSharedGenerator)
    (hNoLocal : ∀ R ∈ regions, H.NoLocalLogical R)
    (P : Binary ι) (hP : H.code.1.InBinaryNormalizer P) :
    ∃ S : Binary ι,
      S ∈ H.code.1.generatedGroup ∧
      H.code.1.InBinaryNormalizer (binaryMul P S) ∧
      support (binaryMul P S) ⊆ (regionUnion regions)ᶜ := by
  induction regions generalizing P with
  | nil =>
      refine ⟨binaryOne, ?_, ?_, ?_⟩
      · rw [← H.generated_eq]
        exact GeneratedStabilizer.one
      · simpa using hP
      · simp [regionUnion]
  | cons R regions ih =>
      have hpairTail : regions.Pairwise H.NoSharedGenerator := hpairwise.tail
      have hNoLocalTail : ∀ T ∈ regions, H.NoLocalLogical T := by
        intro T hT
        exact hNoLocal T (by simp [hT])
      obtain ⟨S₀, hS₀, hP₀, hOutsideTail⟩ :=
        ih hpairTail hNoLocalTail P hP
      have hNoLocalR : H.NoLocalLogical R :=
        hNoLocal R (by simp)
      have hCleanR :
          ∃ S₁ : Binary ι,
            H.GeneratedByMeeting R S₁ ∧
            S₁ ∈ H.code.1.generatedGroup ∧
            H.code.1.InBinaryNormalizer
              (binaryMul (binaryMul P S₀) S₁) ∧
            support (binaryMul (binaryMul P S₀) S₁) ⊆ Rᶜ := by
        rcases H.stabilizerCleaningDichotomy R with hlocal | hclean
        · exact (hNoLocalR hlocal).elim
        · exact hclean (binaryMul P S₀) hP₀
      obtain ⟨S₁, hS₁Meeting, hS₁, hP₁, hOutsideR⟩ := hCleanR
      have hSeparatedTail :
          H.NoSharedGenerator R (regionUnion regions) :=
        H.noSharedGenerator_regionUnion R regions
          (List.pairwise_cons.mp hpairwise).1
      have hS₁Disjoint :
          Disjoint (support S₁) (regionUnion regions) :=
        H.disjoint_support_of_generatedByMeeting_of_noSharedGenerator
          R (regionUnion regions) S₁ hSeparatedTail hS₁Meeting
      have hOutsideTailAfter :
          support (binaryMul (binaryMul P S₀) S₁) ⊆
            (regionUnion regions)ᶜ := by
        intro i hi
        apply Finset.mem_compl.mpr
        intro hiUnion
        rcases Finset.mem_union.mp
            (support_binaryMul_subset (binaryMul P S₀) S₁ hi) with hiP₀ | hiS₁
        · exact (Finset.mem_compl.mp (hOutsideTail hiP₀)) hiUnion
        · exact (Finset.disjoint_left.mp hS₁Disjoint hiS₁ hiUnion)
      refine ⟨binaryMul S₀ S₁, ?_, ?_, ?_⟩
      · rw [← H.generated_eq] at hS₀ hS₁ ⊢
        exact GeneratedStabilizer.mul hS₀ hS₁
      · simpa [binaryMul_assoc] using hP₁
      · intro i hi
        have hi' :
            i ∈ support (binaryMul (binaryMul P S₀) S₁) := by
          simpa [binaryMul_assoc] using hi
        apply Finset.mem_compl.mpr
        intro hiUnion
        rcases Finset.mem_union.mp hiUnion with hiR | hiTail
        · exact (Finset.mem_compl.mp (hOutsideR hi')) hiR
        · exact (Finset.mem_compl.mp (hOutsideTailAfter hi')) hiTail

/--
Multiplication by an actual generated stabilizer preserves the nontrivial
logical coset.  This is kept in the strip module so that the BT09 distance
route depends only on the cleaning API, rather than on the later path-energy
module.
-/
theorem logicalCoset_binaryMul_generated_iff_for_strip_cleaning
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E S : Binary ι) (hS : S ∈ H.code.1.generatedGroup) :
    (H.code.1.InBinaryNormalizer (binaryMul E S) ∧
        ¬ H.code.1.InGeneratedGroupUpToSign (binaryMul E S)) ↔
      (H.code.1.InBinaryNormalizer E ∧
        ¬ H.code.1.InGeneratedGroupUpToSign E) := by
  let V := H.code.1.generatedVectorSubspace
  have hSV : S.vector ∈ V :=
    (H.code.1.vector_mem_generatedVectorSubspace_iff S).2
      ⟨S, hS, rfl⟩
  have hSOrth :
      S.vector ∈ FiniteSymplectic.form.orthogonal V :=
    H.code.1.generatedVectorSubspace_isotropic hSV
  rw [← H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer,
    ← H.code.1.vector_mem_generatedVectorSubspace_iff,
    ← H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer,
    ← H.code.1.vector_mem_generatedVectorSubspace_iff]
  change
    (E.vector + S.vector ∈ FiniteSymplectic.form.orthogonal V ∧
        E.vector + S.vector ∉ V) ↔
      (E.vector ∈ FiniteSymplectic.form.orthogonal V ∧ E.vector ∉ V)
  rw [(FiniteSymplectic.form.orthogonal V).add_mem_iff_left hSOrth,
    V.add_mem_iff_left hSV]

/--
The abstract alternating-strip step of BT09.  Cleaning every region in the
first family leaves a representative supported on the second family; one
generator-separated member of that family then carries a nontrivial logical
restriction.
-/
theorem exists_logical_supported_in_remaining_region
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (cleanedRegions remainingRegions : List (Finset ι))
    (hCleanedSeparated :
      cleanedRegions.Pairwise H.NoSharedGenerator)
    (hRemainingDisjoint : remainingRegions.Pairwise Disjoint)
    (hRemainingSeparated :
      remainingRegions.Pairwise H.NoSharedGenerator)
    (hCover :
      regionUnion cleanedRegions ∪ regionUnion remainingRegions =
        (Finset.univ : Finset ι))
    (hNoLocal : ∀ R ∈ cleanedRegions, H.NoLocalLogical R)
    (P : Binary ι)
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ R ∈ remainingRegions, ∃ Q : Binary ι,
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      support Q ⊆ R := by
  obtain ⟨S, hS, hCleanedNormalizer, hOutside⟩ :=
    H.exists_cleanedOutside_regionUnion
      cleanedRegions hCleanedSeparated hNoLocal P hPNormalizer
  have hCleanedNontrivial :
      ¬ H.code.1.InGeneratedGroupUpToSign (binaryMul P S) :=
    ((H.logicalCoset_binaryMul_generated_iff_for_strip_cleaning P S hS).2
      ⟨hPNormalizer, hPNontrivial⟩).2
  have hSupportedRemaining :
      support (binaryMul P S) ⊆ regionUnion remainingRegions := by
    intro i hi
    have hiOutside : i ∈ (regionUnion cleanedRegions)ᶜ :=
      hOutside hi
    have hiCover :
        i ∈ regionUnion cleanedRegions ∪ regionUnion remainingRegions := by
      rw [hCover]
      simp
    rcases Finset.mem_union.mp hiCover with hiCleaned | hiRemaining
    · exact (Finset.mem_compl.mp hiOutside hiCleaned).elim
    · exact hiRemaining
  obtain ⟨R, hR, hRNormalizer, hRNontrivial, hRSupport⟩ :=
    H.exists_nontrivial_logical_restriction
      remainingRegions hRemainingDisjoint hRemainingSeparated
      (binaryMul P S) hCleanedNormalizer hCleanedNontrivial
      hSupportedRemaining
  exact
    ⟨R, hR, Locality.restrictBinaryTo R (binaryMul P S),
      hRNormalizer, hRNontrivial, hRSupport⟩

/--
Alternating-strip cleaning without a correctability premise: either a region
in the first parity already carries a nontrivial logical, or all of them can
be cleaned and a region in the second parity carries one.
-/
theorem exists_logical_supported_in_alternating_partition
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (firstRegions secondRegions : List (Finset ι))
    (hFirstSeparated : firstRegions.Pairwise H.NoSharedGenerator)
    (hSecondDisjoint : secondRegions.Pairwise Disjoint)
    (hSecondSeparated : secondRegions.Pairwise H.NoSharedGenerator)
    (hCover :
      regionUnion firstRegions ∪ regionUnion secondRegions =
        (Finset.univ : Finset ι))
    (P : Binary ι)
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ R ∈ firstRegions ++ secondRegions, ∃ Q : Binary ι,
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      support Q ⊆ R := by
  by_cases hNoLocal : ∀ R ∈ firstRegions, H.NoLocalLogical R
  · obtain ⟨R, hR, Q, hQNormalizer, hQNontrivial, hQSupport⟩ :=
      H.exists_logical_supported_in_remaining_region
        firstRegions secondRegions hFirstSeparated hSecondDisjoint
        hSecondSeparated hCover hNoLocal P hPNormalizer hPNontrivial
    exact
      ⟨R, List.mem_append_right firstRegions hR, Q,
        hQNormalizer, hQNontrivial, hQSupport⟩
  · push Not at hNoLocal
    obtain ⟨R, hR, hRLocal⟩ := hNoLocal
    unfold NoLocalLogical at hRLocal
    push Not at hRLocal
    obtain ⟨Q, hQNormalizer, hQNontrivial, hQSupport⟩ := hRLocal
    exact
      ⟨R, List.mem_append_left secondRegions hR, Q,
        hQNormalizer, hQNontrivial, hQSupport⟩

/--
The nondegenerate open-boundary BT09 conclusion: at the exact source
threshold, some nontrivial logical representative is supported in a concrete
vertical strip whose width is `r - 1` or `r`.
-/
theorem exists_bt09_open_strip_logical_of_two_le_range
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ start width, (width = r - 1 ∨ width = r) ∧
      ∃ Q : Binary (StripGeometry.Site L),
        H.code.1.InBinaryNormalizer Q ∧
        ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
        support Q ⊆
          StripGeometry.openVerticalInterval L start width := by
  let D : AlternatingWidthDecomposition L r :=
    Classical.choice (exists_alternatingWidthDecomposition hr hL)
  let strips :=
    StripGeometry.openStripListAux L 0 D.widths
  let firstRegions := StripGeometry.firstParity strips
  let secondRegions := StripGeometry.secondParity strips
  have hWidthLower : ∀ width ∈ D.widths, r - 1 ≤ width := by
    intro width hwidth
    rcases D.width_eq width hwidth with hEq | hEq <;> omega
  have hAllDisjoint : strips.Pairwise Disjoint :=
    StripGeometry.openStripListAux_pairwise_disjoint L 0 D.widths
  have hFirstSeparated :
      firstRegions.Pairwise H.NoSharedGenerator := by
    have hGeometry :=
      StripGeometry.firstParity_open_pairwise_intervalSeparated
        L r 0 D.widths hWidthLower
    exact hGeometry.imp fun h =>
      H.noSharedGenerator_of_openIntervalSeparated r _ _ hLocal h
  have hSecondSeparated :
      secondRegions.Pairwise H.NoSharedGenerator := by
    have hGeometry :=
      StripGeometry.secondParity_open_pairwise_intervalSeparated
        L r 0 D.widths hWidthLower
    exact hGeometry.imp fun h =>
      H.noSharedGenerator_of_openIntervalSeparated r _ _ hLocal h
  have hSecondDisjoint : secondRegions.Pairwise Disjoint :=
    StripGeometry.secondParity_pairwise hAllDisjoint
  have hCover :
      regionUnion firstRegions ∪ regionUnion secondRegions =
        (Finset.univ : Finset (StripGeometry.Site L)) := by
    calc
      regionUnion firstRegions ∪ regionUnion secondRegions =
          regionUnion strips := by
            exact
              StripGeometry.regionUnion_firstParity_union_secondParity
                strips
      _ = (Finset.univ : Finset (StripGeometry.Site L)) := by
            exact StripGeometry.regionUnion_openStrips_eq_univ D
  obtain ⟨R, hR, Q, hQNormalizer, hQNontrivial, hQSupport⟩ :=
    H.exists_logical_supported_in_alternating_partition
      firstRegions secondRegions hFirstSeparated hSecondDisjoint
      hSecondSeparated hCover P hPNormalizer hPNontrivial
  have hRStrips : R ∈ strips := by
    rcases List.mem_append.mp hR with hFirst | hSecond
    · exact (StripGeometry.firstParity_sublist strips).subset hFirst
    · exact (StripGeometry.secondParity_sublist strips).subset hSecond
  obtain ⟨start, width, hwidth, rfl⟩ :=
    StripGeometry.mem_openStripListAux_exists hRStrips
  exact
    ⟨start, width, D.width_eq width hwidth, Q,
      hQNormalizer, hQNontrivial, hQSupport⟩

/--
The corresponding periodic-boundary BT09 conclusion.  The same internally
constructed strips are used, while generator locality is witnessed by actual
cyclic intervals; the even strip count supplies the seam separation.
-/
theorem exists_bt09_periodic_strip_logical_of_two_le_range
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasPeriodicIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ start width, (width = r - 1 ∨ width = r) ∧
      ∃ Q : Binary (StripGeometry.Site L),
        H.code.1.InBinaryNormalizer Q ∧
        ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
        support Q ⊆
          StripGeometry.openVerticalInterval L start width := by
  let D : AlternatingWidthDecomposition L r :=
    Classical.choice (exists_alternatingWidthDecomposition hr hL)
  let strips :=
    StripGeometry.openStripListAux L 0 D.widths
  let firstRegions := StripGeometry.firstParity strips
  let secondRegions := StripGeometry.secondParity strips
  have hWidthLower : ∀ width ∈ D.widths, r - 1 ≤ width := by
    intro width hwidth
    rcases D.width_eq width hwidth with hEq | hEq <;> omega
  have hAllDisjoint : strips.Pairwise Disjoint :=
    StripGeometry.openStripListAux_pairwise_disjoint L 0 D.widths
  have hFirstSeparated :
      firstRegions.Pairwise H.NoSharedGenerator := by
    have hGeometry :=
      StripGeometry.firstParity_periodic_pairwise_intervalSeparated
        L r D.widths D.sum_widths D.even_length hWidthLower
    exact hGeometry.imp fun h =>
      H.noSharedGenerator_of_periodicIntervalSeparated r _ _ hLocal h
  have hSecondSeparated :
      secondRegions.Pairwise H.NoSharedGenerator := by
    have hGeometry :=
      StripGeometry.secondParity_periodic_pairwise_intervalSeparated
        L r D.widths hWidthLower
    exact hGeometry.imp fun h =>
      H.noSharedGenerator_of_periodicIntervalSeparated r _ _ hLocal h
  have hSecondDisjoint : secondRegions.Pairwise Disjoint :=
    StripGeometry.secondParity_pairwise hAllDisjoint
  have hCover :
      regionUnion firstRegions ∪ regionUnion secondRegions =
        (Finset.univ : Finset (StripGeometry.Site L)) := by
    calc
      regionUnion firstRegions ∪ regionUnion secondRegions =
          regionUnion strips := by
            exact
              StripGeometry.regionUnion_firstParity_union_secondParity
                strips
      _ = (Finset.univ : Finset (StripGeometry.Site L)) := by
            exact StripGeometry.regionUnion_openStrips_eq_univ D
  obtain ⟨R, hR, Q, hQNormalizer, hQNontrivial, hQSupport⟩ :=
    H.exists_logical_supported_in_alternating_partition
      firstRegions secondRegions hFirstSeparated hSecondDisjoint
      hSecondSeparated hCover P hPNormalizer hPNontrivial
  have hRStrips : R ∈ strips := by
    rcases List.mem_append.mp hR with hFirst | hSecond
    · exact (StripGeometry.firstParity_sublist strips).subset hFirst
    · exact (StripGeometry.secondParity_sublist strips).subset hSecond
  obtain ⟨start, width, hwidth, rfl⟩ :=
    StripGeometry.mem_openStripListAux_exists hRStrips
  exact
    ⟨start, width, D.width_eq width hwidth, Q,
      hQNormalizer, hQNontrivial, hQSupport⟩

/-- Explicit open-boundary linear-support form of the BT09 proposition. -/
theorem exists_bt09_open_logical_support_card_le
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ r * L := by
  obtain ⟨start, width, hwidth, Q,
    hQNormalizer, hQNontrivial, hQSupport⟩ :=
    H.exists_bt09_open_strip_logical_of_two_le_range
      hr hL hLocal P hPNormalizer hPNontrivial
  have hwidthLe : width ≤ r := by
    rcases hwidth with rfl | rfl <;> omega
  refine ⟨Q, hQNormalizer, hQNontrivial, ?_⟩
  exact
    (Finset.card_le_card hQSupport).trans
      ((StripGeometry.card_openVerticalInterval_le L start width).trans
        (Nat.mul_le_mul_right L hwidthLe))

/-- Explicit periodic-boundary linear-support form of the BT09 proposition. -/
theorem exists_bt09_periodic_logical_support_card_le
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasPeriodicIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ r * L := by
  obtain ⟨start, width, hwidth, Q,
    hQNormalizer, hQNontrivial, hQSupport⟩ :=
    H.exists_bt09_periodic_strip_logical_of_two_le_range
      hr hL hLocal P hPNormalizer hPNontrivial
  have hwidthLe : width ≤ r := by
    rcases hwidth with rfl | rfl <;> omega
  refine ⟨Q, hQNormalizer, hQNontrivial, ?_⟩
  exact
    (Finset.card_le_card hQSupport).trans
      ((StripGeometry.card_openVerticalInterval_le L start width).trans
        (Nat.mul_le_mul_right L hwidthLe))

/-- The explicit degenerate `r = 1` open-boundary branch. -/
theorem exists_bt09_open_unit_range_logical_support_card_le
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H 1)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ L := by
  let widths := List.replicate L 1
  let regions := StripGeometry.openStripListAux L 0 widths
  have hPositive : ∀ width ∈ widths, 1 ≤ width := by
    intro width hwidth
    have := List.eq_of_mem_replicate hwidth
    omega
  have hDisjoint : regions.Pairwise Disjoint :=
    StripGeometry.openStripListAux_pairwise_disjoint L 0 widths
  have hSeparated : regions.Pairwise H.NoSharedGenerator := by
    have hGeometry :=
      StripGeometry.openStripListAux_pairwise_openUnitSeparated
        L 0 widths hPositive
    exact hGeometry.imp fun h =>
      H.noSharedGenerator_of_openIntervalSeparated 1 _ _ hLocal h
  have hCover :
      regionUnion regions =
        (Finset.univ : Finset (StripGeometry.Site L)) := by
    rw [StripGeometry.regionUnion_openStripListAux]
    simp [widths]
    ext p
    simp
  have hSupport : support P ⊆ regionUnion regions := by
    rw [hCover]
    exact Finset.subset_univ _
  obtain ⟨R, hR, hRNormalizer, hRNontrivial, hRSupport⟩ :=
    H.exists_nontrivial_logical_restriction
      regions hDisjoint hSeparated P hPNormalizer hPNontrivial hSupport
  obtain ⟨start, width, hwidth, rfl⟩ :=
    StripGeometry.mem_openStripListAux_exists hR
  have hwidthEq : width = 1 :=
    List.eq_of_mem_replicate hwidth
  subst width
  refine
    ⟨Locality.restrictBinaryTo
        (StripGeometry.openVerticalInterval L start 1) P,
      hRNormalizer, hRNontrivial, ?_⟩
  exact
    (Finset.card_le_card hRSupport).trans
      (by simpa using
        StripGeometry.card_openVerticalInterval_le L start 1)

/-- The explicit degenerate `r = 1` periodic-boundary branch. -/
theorem exists_bt09_periodic_unit_range_logical_support_card_le
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hLocal : StripGeometry.HasPeriodicIntervalGeneratorSupport H 1)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ L := by
  let widths := List.replicate L 1
  let regions := StripGeometry.openStripListAux L 0 widths
  have hPositive : ∀ width ∈ widths, 1 ≤ width := by
    intro width hwidth
    have := List.eq_of_mem_replicate hwidth
    omega
  have hDisjoint : regions.Pairwise Disjoint :=
    StripGeometry.openStripListAux_pairwise_disjoint L 0 widths
  have hSeparated : regions.Pairwise H.NoSharedGenerator := by
    have hGeometry :=
      StripGeometry.openStripListAux_pairwise_periodicUnitSeparated
        L widths hPositive
    exact hGeometry.imp fun h =>
      H.noSharedGenerator_of_periodicIntervalSeparated 1 _ _ hLocal h
  have hCover :
      regionUnion regions =
        (Finset.univ : Finset (StripGeometry.Site L)) := by
    rw [StripGeometry.regionUnion_openStripListAux]
    simp [widths]
    ext p
    simp
  have hSupport : support P ⊆ regionUnion regions := by
    rw [hCover]
    exact Finset.subset_univ _
  obtain ⟨R, hR, hRNormalizer, hRNontrivial, hRSupport⟩ :=
    H.exists_nontrivial_logical_restriction
      regions hDisjoint hSeparated P hPNormalizer hPNontrivial hSupport
  obtain ⟨start, width, hwidth, rfl⟩ :=
    StripGeometry.mem_openStripListAux_exists hR
  have hwidthEq : width = 1 :=
    List.eq_of_mem_replicate hwidth
  subst width
  refine
    ⟨Locality.restrictBinaryTo
        (StripGeometry.openVerticalInterval L start 1) P,
      hRNormalizer, hRNontrivial, ?_⟩
  exact
    (Finset.card_le_card hRSupport).trans
      (by simpa using
        StripGeometry.card_openVerticalInterval_le L start 1)

/--
BT09's open-boundary linear-distance proposition, including the explicit
`r = 1` branch and the exact `L ≥ 2(r-1)^2` threshold.
-/
theorem bt09_open_linear_distance
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 1 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ r * L := by
  by_cases hrOne : r = 1
  · subst r
    simpa using
      H.exists_bt09_open_unit_range_logical_support_card_le
        hLocal P hPNormalizer hPNontrivial
  · have hrTwo : 2 ≤ r := by omega
    exact
      H.exists_bt09_open_logical_support_card_le
        hrTwo hL hLocal P hPNormalizer hPNontrivial

/--
BT09's periodic-boundary linear-distance proposition, with the cyclic seam
handled by the internally constructed even strip decomposition.
-/
theorem bt09_periodic_linear_distance
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 1 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasPeriodicIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ r * L := by
  by_cases hrOne : r = 1
  · subst r
    simpa using
      H.exists_bt09_periodic_unit_range_logical_support_card_le
        hLocal P hPNormalizer hPNontrivial
  · have hrTwo : 2 ≤ r := by omega
    exact
      H.exists_bt09_periodic_logical_support_card_le
        hrTwo hL hLocal P hPNormalizer hPNontrivial

end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC
