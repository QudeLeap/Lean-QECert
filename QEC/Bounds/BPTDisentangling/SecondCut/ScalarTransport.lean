import QEC.Bounds.BPTDisentangling.SecondCut.ProjectionBlock

/-!
# BPT second-cut scalar-compression transport

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
Extend an operator on a left-isotypic subtype by zero off that subtype.  This
is the physical `AB` probe used to turn hM no-information into a scalar
equation on the selected BV03 block.
-/
noncomputable def overlapLeftSubtypeLift
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (p : Submodule Complex B)
    (E : Semantics.Operator (Semantics.CompositeSystem A p)) :
    Semantics.Operator (Semantics.CompositeSystem A B) :=
  let K := TensorProduct.map (1 : Semantics.Operator A) p.subtype
  let Kadj := TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint p.subtype)
  K.comp (E.comp Kadj)

/--
Compressing the zero-extended subtype probe through the triple sector
embedding recovers the literal subtype probe on the left overlap factor.
-/
theorem adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_subtypeLift_comp
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) (E : Semantics.Operator (Semantics.CompositeSystem A p)) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)).comp
      ((overlapLiftLeft (C := C) (overlapLeftSubtypeLift p E)).comp
        (tensorTripleSubtypeEmbedding (A := A) (C := C) p)) =
      overlapLiftLeft (C := C) E := by
  let K : (Semantics.CompositeSystem A p) →ₗ[Complex]
      Semantics.CompositeSystem A B :=
    TensorProduct.map (1 : Semantics.Operator A) p.subtype
  let Kadj : (Semantics.CompositeSystem A B) →ₗ[Complex]
      Semantics.CompositeSystem A p :=
    TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint p.subtype)
  have hK : Kadj.comp K = (1 : Semantics.Operator (Semantics.CompositeSystem A p)) := by
    dsimp [K, Kadj]
    rw [← TensorProduct.map_comp]
    rw [adjoint_submoduleSubtype_comp_subtype_eq_one p]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id) LinearMap.id = LinearMap.id
    rw [LinearMap.id_comp]
    exact TensorProduct.map_one
  have hKadj : LinearMap.adjoint K = Kadj := by
    dsimp [K, Kadj]
    rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  let J := tensorTripleSubtypeEmbedding (A := A) (C := C) p
  have hJ : J = TensorProduct.map K (1 : Semantics.Operator C) := by rfl
  have hJadj : LinearMap.adjoint J = TensorProduct.map Kadj (1 : Semantics.Operator C) := by
    rw [hJ, TensorProduct.adjoint_map, hKadj, LinearMap.adjoint_one]
  have hLift : overlapLeftSubtypeLift p E = K.comp (E.comp Kadj) := by rfl
  change (LinearMap.adjoint J).comp
      ((overlapLiftLeft (C := C) (overlapLeftSubtypeLift p E)).comp J) =
      overlapLiftLeft (C := C) E
  rw [hJadj, hJ, hLift]
  unfold overlapLiftLeft
  rw [← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  congr 1
  calc
    Kadj.comp ((K.comp (E.comp Kadj)).comp K) =
        Kadj.comp (K.comp (E.comp (Kadj.comp K))) := by
      simp only [LinearMap.comp_assoc]
    _ = Kadj.comp (K.comp (E.comp (1 : Semantics.Operator (Semantics.CompositeSystem A p)))) := by
      rw [hK]
    _ = Kadj.comp (K.comp E) := by
      apply LinearMap.ext
      intro vector
      rfl
    _ = (Kadj.comp K).comp E := by rw [LinearMap.comp_assoc]
    _ = E := by rw [hK]; rfl

/-- Scalar compression descends through a two-sided compressed coordinate block. -/
theorem compressed_scalar_of_two_sided_intertwining
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (R L : Semantics.Operator K) (Rsub Lsub : Semantics.Operator H)
    (scalar : Complex)
    (hRleft : Jadj.comp R = Rsub.comp Jadj)
    (hRright : R.comp J = J.comp Rsub)
    (hprobe : Jadj.comp (L.comp J) = Lsub)
    (hRsub : Rsub = Jadj.comp (R.comp J))
    (hscalar : R * L * R = scalar • R) :
    Rsub * Lsub * Rsub = scalar • Rsub := by
  have hcongr := congrArg (fun operator => Jadj.comp (operator.comp J)) hscalar
  have hleftSide : Jadj.comp (((R * L) * R).comp J) =
      Rsub * Lsub * Rsub := by
    calc
      Jadj.comp (((R * L) * R).comp J) =
          (Jadj.comp R).comp (L.comp (R.comp J)) := by
        simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
      _ = (Rsub.comp Jadj).comp (L.comp (J.comp Rsub)) := by
        rw [hRleft, hRright]
      _ = Rsub.comp ((Jadj.comp (L.comp J)).comp Rsub) := by
        simp only [LinearMap.comp_assoc]
      _ = Rsub.comp (Lsub.comp Rsub) := by rw [hprobe]
      _ = Rsub * Lsub * Rsub := by
        simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  calc
    Rsub * Lsub * Rsub = Jadj.comp (((R * L) * R).comp J) := hleftSide.symm
    _ = Jadj.comp ((scalar • R).comp J) := hcongr
    _ = scalar • (Jadj.comp (R.comp J)) := by
      apply LinearMap.ext
      intro vector
      simp [LinearMap.comp_apply]
    _ = scalar • Rsub := by rw [hRsub]

/--
An isometric reconstruction can expose a named compressed block without
repeating its `J† R J` expression in every downstream physical statement.
-/
theorem compressed_scalar_of_named_isometric_reconstruction
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (R L : Semantics.Operator K)
    (Rsub Lsub : Semantics.Operator H) (scalar : Complex)
    (hJadj : (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H))
    (hreconstruct : R = J.comp (Rsub.comp (LinearMap.adjoint J)))
    (hprobe : (LinearMap.adjoint J).comp (L.comp J) = Lsub)
    (hscalar : R * L * R = scalar • R) :
    Rsub * Lsub * Rsub = scalar • Rsub := by
  let Jadj := LinearMap.adjoint J
  have hreconstruct' : R = J.comp (Rsub.comp Jadj) := hreconstruct
  have hRleft : Jadj.comp R = Rsub.comp Jadj := by
    calc
      Jadj.comp R = Jadj.comp (J.comp (Rsub.comp Jadj)) := by rw [hreconstruct']
      _ = (Jadj.comp J).comp (Rsub.comp Jadj) := by rw [← LinearMap.comp_assoc]
      _ = Rsub.comp Jadj := by rw [hJadj]; rfl
  have hRright : R.comp J = J.comp Rsub := by
    calc
      R.comp J = (J.comp (Rsub.comp Jadj)).comp J := by rw [hreconstruct']
      _ = J.comp (Rsub.comp (Jadj.comp J)) := by simp only [LinearMap.comp_assoc]
      _ = J.comp (Rsub.comp (1 : Semantics.Operator H)) := by rw [hJadj]
      _ = J.comp Rsub := by rfl
  have hRsub : Rsub = Jadj.comp (R.comp J) := by
    symm
    calc
      Jadj.comp (R.comp J) = (Jadj.comp R).comp J := by rw [← LinearMap.comp_assoc]
      _ = (Rsub.comp Jadj).comp J := by rw [hRleft]
      _ = Rsub.comp (Jadj.comp J) := by rw [LinearMap.comp_assoc]
      _ = Rsub.comp (1 : Semantics.Operator H) := by rw [hJadj]
      _ = Rsub := by rfl
  exact compressed_scalar_of_two_sided_intertwining
    J Jadj R L Rsub Lsub scalar hRleft hRright hprobe hRsub hscalar

/--
An isometric reconstruction supplies the two intertwining equations needed to
compress a scalar relation.  Keeping this algebra generic prevents the BPT
coordinate terms from being unfolded while the relation is transported.
-/
theorem compressed_scalar_of_isometric_reconstruction
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (R L : Semantics.Operator K)
    (Lsub : Semantics.Operator H) (scalar : Complex)
    (hJadj : (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H))
    (hreconstruct : R = J.comp
      (((LinearMap.adjoint J).comp (R.comp J)).comp (LinearMap.adjoint J)))
    (hprobe : (LinearMap.adjoint J).comp (L.comp J) = Lsub)
    (hscalar : R * L * R = scalar • R) :
    ((LinearMap.adjoint J).comp (R.comp J)) * Lsub *
        ((LinearMap.adjoint J).comp (R.comp J)) =
      scalar • ((LinearMap.adjoint J).comp (R.comp J)) := by
  exact compressed_scalar_of_named_isometric_reconstruction
    J R L ((LinearMap.adjoint J).comp (R.comp J)) Lsub scalar hJadj
      hreconstruct hprobe hscalar

end BPTCommutingProjectorModel

end Bounds
end QEC
