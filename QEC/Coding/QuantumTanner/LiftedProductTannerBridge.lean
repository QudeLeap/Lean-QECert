import QEC.Coding.QuantumTanner.LiftedProductTensorBridge

/-!
# Selected lifted-product and quadripartite Tanner check spaces

The four group arguments below are the labelled square charts in
[LZDec22, Section "Labelling Q-neighbourhoods"], followed by the selected
construction in Section "Quantum Tanner codes from Lifted Product codes".
The Z family uses the two opposite charts with arguments `g b` and `a g`;
the X family uses the other two, `g` and `a g b`. These are labelled
quadripartite squares, not a quotient requiring total no-conjugacy.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LiftedProductTannerBridge

open Classical
open LiftedProductRestriction LiftedProductActionBridge LiftedProductTensorBridge

universe v

variable {G A B C D C' D' : Type v} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']

/-- Actual selected Z checks, restricted from the second lifted-product boundary. -/
def selectedZWord (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gB : Matrix D' B (ZMod 2)) (a : A → G) (b : B → G)
    (U : Matrix C D' (MonoidAlgebra (ZMod 2) G) ×
      Matrix C D' (MonoidAlgebra (ZMod 2) G)) : Word (ZMod 2) (A × B × G) :=
  fun (i, j, g) => zWord hA hB a b
    (zParameter (U.1 * twistedMatrix gB (fun j => (b j)⁻¹)) (U.2 * scalarMatrix gB))
    (retainedCoordinate i j g)

/-- Actual selected X checks, restricted from the transposed first boundary. -/
def selectedXWord (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (a : A → G) (b : B → G)
    (V : Matrix C' D (MonoidAlgebra (ZMod 2) G) ×
      Matrix C' D (MonoidAlgebra (ZMod 2) G)) : Word (ZMod 2) (A × B × G) :=
  fun (i, j, g) => xWord hA hB a b
    (xParameter ((scalarMatrix gA).transpose * V.1)
      ((twistedMatrix gA (fun i => (a i)⁻¹)).transpose * V.2))
    (retainedCoordinate i j g)

/-- A group-algebra parameter gives one local tensor-code word at each group vertex. -/
def parameterSections (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2))
    (U : Matrix C D (MonoidAlgebra (ZMod 2) G)) :
    G → (tensorCode (matrixRowCode P) (matrixRowCode Q)).carrier :=
  fun u => ⟨tensorMatrix P Q (fun c d => (U c d).coeff u), tensorMatrix_mem P Q _⟩

/-- Coefficient extraction of the actual selected Z boundary gives the two source charts. -/
theorem selectedZWord_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G)
    (U : Matrix C D' (MonoidAlgebra (ZMod 2) G) ×
      Matrix C D' (MonoidAlgebra (ZMod 2) G)) (i : A) (j : B) (g : G) :
    selectedZWord hA hB gB a b U (i, j, g) =
      (parameterSections hA gB U.1 (g * b j)).val (i, j) +
        (parameterSections hA gB U.2 (a i * g)).val (i, j) := by
  rw [selectedZWord, zWord_retained_coeff]
  change (∑ c, hA c i * (∑ d, U.1 c d * MonoidAlgebra.single ((b j)⁻¹) (gB d j)).coeff g) +
    (∑ c, hA c i * (∑ d, U.2 c d * MonoidAlgebra.single 1 (gB d j)).coeff (a i * g)) = _
  simp [parameterSections, tensorMatrix,
    MonoidAlgebra.coeff_mul_single_apply, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Coefficient extraction of the actual selected X boundary gives the other two charts. -/
theorem selectedXWord_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (gA : Matrix C' A (ZMod 2))
    (a : A → G) (b : B → G)
    (V : Matrix C' D (MonoidAlgebra (ZMod 2) G) ×
      Matrix C' D (MonoidAlgebra (ZMod 2) G)) (i : A) (j : B) (g : G) :
    selectedXWord hA hB gA a b V (i, j, g) =
      (parameterSections gA hB V.1 g).val (i, j) +
        (parameterSections gA hB V.2 (a i * g * b j)).val (i, j) := by
  rw [selectedXWord, xWord_retained_coeff]
  change (∑ d, hB d j * (∑ c, MonoidAlgebra.single 1 (gA c i) * V.1 c d).coeff g) +
    (∑ d, hB d j * (∑ c, MonoidAlgebra.single ((a i)⁻¹) (gA c i) * V.2 c d).coeff (g * b j)) = _
  simp [parameterSections, tensorMatrix,
    MonoidAlgebra.coeff_single_mul_apply, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  congr 1 <;> exact Finset.sum_comm

/-- Every family of genuine local tensor words has group-algebra parameters.
Finite coefficient packing is used only after the local factorization theorem. -/
theorem parameterSections_surjective (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2)) :
    Function.Surjective (parameterSections (G := G) P Q) := by
  intro T
  have h : ∀ u : G, ∃ U : Matrix C D (ZMod 2), tensorMatrix P Q U = (T u).val :=
    fun u => (mem_tensorCode_iff_tensorMatrix P Q (T u).val).1 (T u).property
  choose U hU using h
  let packed : Matrix C D (MonoidAlgebra (ZMod 2) G) :=
    fun c d => MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (fun u => U u c d))
  refine ⟨packed, ?_⟩
  funext u
  apply Subtype.ext
  change tensorMatrix P Q (fun c d => (packed c d).coeff u) = (T u).val
  rw [← hU u]
  congr 1

/-- The local tensor sections on the two Z vertex parts, extended along their labelled charts. -/
def tannerZMap (a : A → G) (b : B → G) (L : LinearCode (ZMod 2) (A × B)) :
    ((G → L.carrier) × (G → L.carrier)) →ₗ[ZMod 2] Word (ZMod 2) (A × B × G) where
  toFun T := fun (i, j, g) => (T.1 (g * b j)).val (i, j) + (T.2 (a i * g)).val (i, j)
  map_add' T S := by ext ⟨i, j, g⟩; simp [add_assoc, add_left_comm, add_comm]
  map_smul' k T := by ext ⟨i, j, g⟩; simp [mul_add]

/-- The local tensor sections on the two X vertex parts, extended along their labelled charts. -/
def tannerXMap (a : A → G) (b : B → G) (L : LinearCode (ZMod 2) (A × B)) :
    ((G → L.carrier) × (G → L.carrier)) →ₗ[ZMod 2] Word (ZMod 2) (A × B × G) where
  toFun T := fun (i, j, g) => (T.1 g).val (i, j) + (T.2 (a i * g * b j)).val (i, j)
  map_add' T S := by ext ⟨i, j, g⟩; simp [add_assoc, add_left_comm, add_comm]
  map_smul' k T := by ext ⟨i, j, g⟩; simp [mul_add]

/-- Exact Z check-space identification, with both image inclusions witnessed by parameters. -/
theorem selectedZ_range_eq_tanner (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (gB : Matrix D' B (ZMod 2)) (a : A → G) (b : B → G) :
    Set.range (selectedZWord hA hB gB a b) =
      (LinearMap.range (tannerZMap a b (tensorCode (matrixRowCode hA) (matrixRowCode gB)))).carrier := by
  ext x
  constructor
  · rintro ⟨U, rfl⟩
    refine ⟨(parameterSections hA gB U.1, parameterSections hA gB U.2), ?_⟩
    ext ⟨i, j, g⟩
    exact (selectedZWord_coeff hA hB gB a b U i j g).symm
  · rintro ⟨T, rfl⟩
    obtain ⟨U0, hU0⟩ := parameterSections_surjective hA gB T.1
    obtain ⟨U1, hU1⟩ := parameterSections_surjective hA gB T.2
    refine ⟨(U0, U1), ?_⟩
    ext ⟨i, j, g⟩
    rw [selectedZWord_coeff, hU0, hU1]
    rfl

/-- Exact X check-space identification, with both image inclusions witnessed by parameters. -/
theorem selectedX_range_eq_tanner (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (gA : Matrix C' A (ZMod 2)) (a : A → G) (b : B → G) :
    Set.range (selectedXWord hA hB gA a b) =
      (LinearMap.range (tannerXMap a b (tensorCode (matrixRowCode gA) (matrixRowCode hB)))).carrier := by
  ext x
  constructor
  · rintro ⟨V, rfl⟩
    refine ⟨(parameterSections gA hB V.1, parameterSections gA hB V.2), ?_⟩
    ext ⟨i, j, g⟩
    exact (selectedXWord_coeff hA hB gA a b V i j g).symm
  · rintro ⟨T, rfl⟩
    obtain ⟨V0, hV0⟩ := parameterSections_surjective gA hB T.1
    obtain ⟨V1, hV1⟩ := parameterSections_surjective gA hB T.2
    refine ⟨(V0, V1), ?_⟩
    ext ⟨i, j, g⟩
    rw [selectedXWord_coeff, hV0, hV1]
    rfl

/-- Vertex of a labelled square in one of its four parts. The first flag
records the left `a` shift, the second the right `b` shift. Thus these
arguments are respectively `g`, `a g`, `g b`, and `a g b`. -/
def chartVertex (a : A → G) (b : B → G) (left right : Bool)
    (i : A) (j : B) (g : G) : G :=
  (if left then a i * g else g) * (if right then b j else 1)

/-- Extension by zero of a local word at one labelled vertex. The labels
`i,j` remain part of the qubit coordinate; no no-conjugacy quotient is used. -/
def chartExtension (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (x : Word (ZMod 2) (A × B)) : Word (ZMod 2) (A × B × G) :=
  fun (i, j, g) => if u = chartVertex a b left right i j g then x (i, j) else 0

/-- The labelled square chart, represented by its `00` group coordinate. -/
def chartLink (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (ij : A × B) : A × B × G :=
  (ij.1, ij.2, (if left then (a ij.1)⁻¹ * u else u) *
    (if right then (b ij.2)⁻¹ else 1))

theorem chartLink_injective (a : A → G) (b : B → G) (left right : Bool) (u : G) :
    Function.Injective (chartLink a b left right u) := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun x : A × B × G => x.1) h
  · exact congrArg (fun x : A × B × G => x.2.1) h

theorem chartLink_eq_iff (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (i : A) (j : B) (g : G) :
    chartLink a b left right u (i, j) = (i, j, g) ↔
      u = chartVertex a b left right i j g := by
  cases left <;> cases right <;>
    simp [chartLink, chartVertex, mul_assoc, inv_mul_eq_iff_eq_mul,
      mul_inv_eq_iff_eq_mul]

/-- The pointwise chart extension is exactly the usual finite link extension,
not a different definition of the desired global check space. -/
theorem chartExtension_eq_sum_single (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (x : Word (ZMod 2) (A × B)) :
    chartExtension a b left right u x =
      ∑ ij : A × B, x ij • Pi.single (chartLink a b left right u ij) 1 := by
  ext ⟨i, j, g⟩
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single (i, j)]
  · have heq : ((i, j, g) = chartLink a b left right u (i, j)) ↔
        u = chartVertex a b left right i j g := by
      rw [eq_comm]
      exact chartLink_eq_iff a b left right u i j g
    simp [chartExtension, Pi.single_apply, heq]
  · intro ij _ hne
    have hn : chartLink a b left right u ij ≠ (i, j, g) := by
      intro he
      apply hne
      apply Prod.ext
      · exact congrArg (fun q : A × B × G => q.1) he
      · exact congrArg (fun q : A × B × G => q.2.1) he
    simp [Pi.single_apply, hn, Ne.symm hn]
  · simp

/-- The local chart in the source is inverted by left/right inverse shifts. -/
theorem chartExtension_at_chart (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (x : Word (ZMod 2) (A × B)) (i : A) (j : B) :
    chartExtension a b left right u x
      (i, j, (if left then (a i)⁻¹ * u else u) *
        (if right then (b j)⁻¹ else 1)) = x (i, j) := by
  cases left <;> cases right <;> simp [chartExtension, chartVertex, mul_assoc]

/-- Away from that vertex neighbourhood the local extension is zero. -/
theorem chartExtension_off_chart (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (x : Word (ZMod 2) (A × B)) (i : A) (j : B) (g : G)
    (h : u ≠ chartVertex a b left right i j g) :
    chartExtension a b left right u x (i, j, g) = 0 := by
  simp [chartExtension, h]

theorem sum_chartExtension (a : A → G) (b : B → G) (left right : Bool)
    (L : LinearCode (ZMod 2) (A × B)) (T : G → L.carrier) :
    (∑ u : G, chartExtension a b left right u (T u).val) =
      fun (i, j, g) => (T (chartVertex a b left right i j g)).val (i, j) := by
  ext ⟨i, j, g⟩
  simp [chartExtension]

theorem tannerZMap_eq_sum_extensions (a : A → G) (b : B → G)
    (L : LinearCode (ZMod 2) (A × B)) (T : (G → L.carrier) × (G → L.carrier)) :
    tannerZMap a b L T =
      (∑ u : G, chartExtension a b false true u (T.1 u).val) +
      (∑ u : G, chartExtension a b true false u (T.2 u).val) := by
  rw [sum_chartExtension, sum_chartExtension]
  ext ⟨i, j, g⟩
  simp [tannerZMap, chartVertex]

theorem tannerXMap_eq_sum_extensions (a : A → G) (b : B → G)
    (L : LinearCode (ZMod 2) (A × B)) (T : (G → L.carrier) × (G → L.carrier)) :
    tannerXMap a b L T =
      (∑ u : G, chartExtension a b false false u (T.1 u).val) +
      (∑ u : G, chartExtension a b true true u (T.2 u).val) := by
  rw [sum_chartExtension, sum_chartExtension]
  ext ⟨i, j, g⟩
  simp [tannerXMap, chartVertex]

/-- Source-defined Z checks: the span of local words extended by zero on
the two vertex parts with arguments `g b` and `a g`. -/
def tannerZChecks (a : A → G) (b : B → G) (L : LinearCode (ZMod 2) (A × B)) :
    Submodule (ZMod 2) (Word (ZMod 2) (A × B × G)) :=
  Submodule.span (ZMod 2)
    (Set.range (fun ux : G × L.carrier => chartExtension a b false true ux.1 ux.2.val) ∪
      Set.range (fun ux : G × L.carrier => chartExtension a b true false ux.1 ux.2.val))

/-- Source-defined X checks: the span on the parts with arguments `g` and `a g b`. -/
def tannerXChecks (a : A → G) (b : B → G) (L : LinearCode (ZMod 2) (A × B)) :
    Submodule (ZMod 2) (Word (ZMod 2) (A × B × G)) :=
  Submodule.span (ZMod 2)
    (Set.range (fun ux : G × L.carrier => chartExtension a b false false ux.1 ux.2.val) ∪
      Set.range (fun ux : G × L.carrier => chartExtension a b true true ux.1 ux.2.val))

theorem tannerZMap_range_eq_checks (a : A → G) (b : B → G)
    (L : LinearCode (ZMod 2) (A × B)) :
    LinearMap.range (tannerZMap a b L) = tannerZChecks a b L := by
  apply le_antisymm
  · rintro x ⟨T, rfl⟩
    rw [tannerZMap_eq_sum_extensions]
    apply Submodule.add_mem
    · apply Submodule.sum_mem
      intro u _
      exact Submodule.subset_span (Or.inl ⟨(u, T.1 u), rfl⟩)
    · apply Submodule.sum_mem
      intro u _
      exact Submodule.subset_span (Or.inr ⟨(u, T.2 u), rfl⟩)
  · apply Submodule.span_le.2
    rintro x (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩)
    · refine ⟨(Pi.single u w, 0), ?_⟩
      ext ⟨i, j, g⟩
      by_cases h : u = g * b j <;>
        simp [tannerZMap, chartExtension, chartVertex, Pi.single_apply, eq_comm, h]
    · refine ⟨(0, Pi.single u w), ?_⟩
      ext ⟨i, j, g⟩
      by_cases h : u = a i * g <;>
        simp [tannerZMap, chartExtension, chartVertex, Pi.single_apply, eq_comm, h]

theorem tannerXMap_range_eq_checks (a : A → G) (b : B → G)
    (L : LinearCode (ZMod 2) (A × B)) :
    LinearMap.range (tannerXMap a b L) = tannerXChecks a b L := by
  apply le_antisymm
  · rintro x ⟨T, rfl⟩
    rw [tannerXMap_eq_sum_extensions]
    apply Submodule.add_mem
    · apply Submodule.sum_mem
      intro u _
      exact Submodule.subset_span (Or.inl ⟨(u, T.1 u), rfl⟩)
    · apply Submodule.sum_mem
      intro u _
      exact Submodule.subset_span (Or.inr ⟨(u, T.2 u), rfl⟩)
  · apply Submodule.span_le.2
    rintro x (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩)
    · refine ⟨(Pi.single u w, 0), ?_⟩
      ext ⟨i, j, g⟩
      by_cases h : u = g <;>
        simp [tannerXMap, chartExtension, chartVertex, Pi.single_apply, eq_comm, h]
    · refine ⟨(0, Pi.single u w), ?_⟩
      ext ⟨i, j, g⟩
      by_cases h : u = a i * g * b j <;>
        simp [tannerXMap, chartExtension, chartVertex, Pi.single_apply, eq_comm, h]

/-- Ordinary finite-field parity-check duality, in the matrix interface used here. -/
theorem matrixRowCode_eq_dual_kernel (P : Matrix C A (ZMod 2)) :
    matrixRowCode P = (parityCheckKernelCode (Matrix.toLin' P)).dual := by
  rw [← parityCheckRowCode_dual_eq_kernelCode, LinearCode.dual_dual_eq]
  rfl

/-- The source's local dual-check premise determines both local generator codes. -/
theorem local_dual_check_row_codes (h : Matrix C A (ZMod 2))
    (g : Matrix C' A (ZMod 2))
    (hDual : parityCheckKernelCode (Matrix.toLin' g) =
      (parityCheckKernelCode (Matrix.toLin' h)).dual) :
    matrixRowCode h = parityCheckKernelCode (Matrix.toLin' g) ∧
      matrixRowCode g = parityCheckKernelCode (Matrix.toLin' h) := by
  constructor
  · rw [matrixRowCode_eq_dual_kernel, hDual]
  · rw [matrixRowCode_eq_dual_kernel, hDual, LinearCode.dual_dual_eq]

/-- Raw matrix orthogonality follows from the local kernel/dual specification. -/
theorem local_dual_check_mul_transpose_eq_zero (h : Matrix C A (ZMod 2))
    (g : Matrix C' A (ZMod 2))
    (hDual : parityCheckKernelCode (Matrix.toLin' g) =
      (parityCheckKernelCode (Matrix.toLin' h)).dual) : g * h.transpose = 0 := by
  have hRow := (local_dual_check_row_codes h g hDual).1
  ext d c
  have hr : (fun i => h c i) ∈ (matrixRowCode h).carrier := by
    apply (mem_matrixRowCode h _).2
    refine ⟨Pi.single c 1, ?_⟩
    intro i
    simp [Pi.single_apply]
  rw [hRow, mem_parityCheckKernelCode] at hr
  change g.mulVec (fun i => h c i) = 0 at hr
  exact congrFun hr d

/-- Deterministic bridge for the selected canonical lifted-product construction.
Both check-space equalities are proved against the span of actual local
extensions on labelled squares. The only code premises specify local dual
parity checks; they are not a global construction-equivalence certificate.
No spectral bound, expansion, no-conjugacy, or goodness claim is made. -/
theorem selected_lifted_product_eq_quantum_tanner
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G)
    (hDualA : parityCheckKernelCode (Matrix.toLin' gA) =
      (parityCheckKernelCode (Matrix.toLin' hA)).dual)
    (hDualB : parityCheckKernelCode (Matrix.toLin' gB) =
      (parityCheckKernelCode (Matrix.toLin' hB)).dual) :
    let CA := parityCheckKernelCode (Matrix.toLin' gA)
    let CB := parityCheckKernelCode (Matrix.toLin' hB)
    Set.range (selectedZWord hA hB gB a b) =
      (tannerZChecks a b (tensorCode CA CB)).carrier ∧
    Set.range (selectedXWord hA hB gA a b) =
      (tannerXChecks a b (tensorCode CA.dual CB.dual)).carrier ∧
    ∀ U V, (∑ j : B, ∑ i : A, ∑ g : G,
      selectedZWord hA hB gB a b U (i, j, g) *
        selectedXWord hA hB gA a b V (i, j, g)) = 0 := by
  dsimp only
  have hArows := local_dual_check_row_codes hA gA hDualA
  have hBrows := local_dual_check_row_codes hB gB hDualB
  refine ⟨?_, ?_, ?_⟩
  · rw [selectedZ_range_eq_tanner, tannerZMap_range_eq_checks, hArows.1, hBrows.2]
  · rw [selectedX_range_eq_tanner, tannerXMap_range_eq_checks,
      matrixRowCode_eq_dual_kernel, matrixRowCode_eq_dual_kernel]
  · intro U V
    exact selected_retained_checks_orthogonal hA hB gA gB a b
      (local_dual_check_mul_transpose_eq_zero hA gA hDualA)
      (local_dual_check_mul_transpose_eq_zero hB gB hDualB) U.1 U.2 V.1 V.2

end QEC.Coding.QuantumTanner.LiftedProductTannerBridge
