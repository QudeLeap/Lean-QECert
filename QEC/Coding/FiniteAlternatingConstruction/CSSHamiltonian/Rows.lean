import QEC.Coding.FiniteAlternatingConstruction.IndexedDecoder
import QEC.Coding.CSS.GibbsSyndrome.Gibbs

/-! # Literal CSS checks on every actual recursive Tanner state -/
noncomputable section
namespace QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26RZMap1CoordinateBridge BDL26LevelTwoDecoder
open PauliSymplectic Semantics
open scoped BigOperators

abbrev presentation (S : OddScale) (n : Nat) := (state S n).presentation
abbrev Physical (S : OddScale) (n : Nat) := (presentation S n).Q
abbrev ZLabel (S : OddScale) (n : Nat) := (presentation S n).Z
abbrev XLabel (S : OddScale) (n : Nat) := (presentation S n).X

variable (S : OddScale) (n : Nat)

/-- Z checks detect X errors through the actual degree-one coboundary. -/
def zSyndrome : Word (ZMod 2) (Physical S n) →ₗ[ZMod 2] Word (ZMod 2) (ZLabel S n) :=
  tannerCoboundary1 (presentation S n)
/-- X checks detect Z errors; the degree-zero coboundary is transposed. -/
def xSyndrome : Word (ZMod 2) (Physical S n) →ₗ[ZMod 2] Word (ZMod 2) (XLabel S n) :=
  wordLinearMapTranspose (tannerCoboundary0 (presentation S n))

private theorem coboundary0_matrix (T : TannerSquarePresentation) :
    tannerCoboundary0 T = wordLinearMapTranspose (Matrix.toLin' (xqIncidenceMatrix T)) := by
  apply LinearMap.ext
  intro e
  funext q
  exact (wordLinearMapTranspose_toLin'_apply (xqIncidenceMatrix T) e q).symm

private theorem coboundary1_matrix (T : TannerSquarePresentation) :
    tannerCoboundary1 T = wordLinearMapTranspose (Matrix.toLin' (qzIncidenceMatrix T)) := by
  apply LinearMap.ext
  intro e
  funext z
  exact (wordLinearMapTranspose_toLin'_apply (qzIncidenceMatrix T) e z).symm

theorem xSyndrome_matrix : xSyndrome S n = Matrix.toLin' (xqIncidenceMatrix (presentation S n)) := by
  rw [xSyndrome, coboundary0_matrix, wordLinearMapTranspose_transpose]

theorem zSyndrome_matrix : zSyndrome S n = Matrix.toLin' (qzIncidenceMatrix (presentation S n)).transpose := by
  ext e z
  simp only [zSyndrome, tannerCoboundary1, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, qzIncidenceMatrix]
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

@[simp] theorem zRow (z : ZLabel S n) (q : Physical S n) :
    parityCheckRow (zSyndrome S n) z q = if (presentation S n).qz q z = true then 1 else 0 := by
  rw [zSyndrome_matrix]
  rw [parityCheckRow, wordLinearMapTranspose_toLin'_apply, Finset.sum_eq_single z]
  · simp [qzIncidenceMatrix]
  · intro r _ hr; simp [Pi.single_apply, hr]
  · simp

@[simp] theorem xRow (x : XLabel S n) (q : Physical S n) :
    parityCheckRow (xSyndrome S n) x q = if (presentation S n).xq x q = true then 1 else 0 := by
  rw [xSyndrome_matrix]
  rw [parityCheckRow, wordLinearMapTranspose_toLin'_apply, Finset.sum_eq_single x]
  · simp [xqIncidenceMatrix]
  · intro r _ hr; simp [Pi.single_apply, hr]
  · simp

theorem row_orthogonal (z : ZLabel S n) (x : XLabel S n) :
    wordPairing (parityCheckRow (zSyndrome S n) z) (parityCheckRow (xSyndrome S n) x) = 0 := by
  have h := congrFun (congrFun (xqIncidenceMatrix_mul_qzIncidenceMatrix (presentation S n)) x) z
  simpa [wordPairing_apply, dotProduct, Matrix.mul_apply, xqIncidenceMatrix,
    qzIncidenceMatrix, mul_comm] using h

/-- Literal transposed presentation, on the very same physical carrier. -/
theorem xSyndrome_transposed : xSyndrome S n = tannerCoboundary1 (transposePresentation (presentation S n)) := by
  rw [xSyndrome_matrix]
  ext e x
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, xqIncidenceMatrix, tannerCoboundary1]
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

abbrev complex := presentationComplex (presentation S n)

theorem xRowCode : parityCheckRowCode (xSyndrome S n) = (complex S n).firstCoboundaryCheckCode := by
  rw [xSyndrome_matrix]
  rfl

theorem zRowCode : parityCheckRowCode (zSyndrome S n) = (complex S n).middleBoundaryCode := by
  have ht : wordLinearMapTranspose (zSyndrome S n) = (complex S n).boundary2 := by
    rw [zSyndrome, coboundary1_matrix, wordLinearMapTranspose_transpose]
    rfl
  simp only [parityCheckRowCode, ChainComplexData.middleBoundaryCode, ht]

/-- Checks retain their Z+X labels; the chain-complex API uses X+Z. -/
def check (j : Sum (ZLabel S n) (XLabel S n)) : Binary (Physical S n) :=
  binaryCSSParityCheckGenerators (zSyndrome S n) (xSyndrome S n) j

theorem check_swap (j : Sum (ZLabel S n) (XLabel S n)) :
    check S n j = QLDPC.chainComplexCSSRowCheck (complex S n) j.swap := by
  cases j with
  | inl z =>
    simp only [check, binaryCSSParityCheckGenerators, Sum.swap_inl, QLDPC.chainComplexCSSRowCheck]
    congr 1
    rw [parityCheckRow, zSyndrome, coboundary1_matrix, wordLinearMapTranspose_transpose]
    rfl
  | inr x =>
    simp only [check, binaryCSSParityCheckGenerators, Sum.swap_inr, QLDPC.chainComplexCSSRowCheck]
    congr 1
    rw [parityCheckRow, xSyndrome_matrix]
    rfl

/-- Equality of the actual semantic carriers, with no dimension assumption. -/
theorem code_carrier :
    (binaryCSSStabilizerCodeOfParityChecks (zSyndrome S n) (xSyndrome S n)
      (row_orthogonal S n)).code.carrier = (complex S n).binaryCSSCode.stabilizer.code.carrier := by
  change (binaryStabilizerCommonFixedQuantumCode
    (binaryCSSCheckSet (parityCheckRowCode (xSyndrome S n)) (parityCheckRowCode (zSyndrome S n)))).carrier = _
  rw [xRowCode, zRowCode]
  rfl

@[simp] theorem check_hermitian (j : Sum (ZLabel S n) (XLabel S n)) :
    toHermitianQubitOperator (check S n j) = toQubitOperator (check S n j) :=
  CSSGibbs.hermitian_row _ _ j

end QEC.Coding.BDL26CSSHamiltonian
