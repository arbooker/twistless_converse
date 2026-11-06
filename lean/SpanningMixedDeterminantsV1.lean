module

public import SpanningLinearHallV1
public import SpanningFiniteFieldTransferV1

@[expose] public section

namespace SpanningMixedDeterminants

open scoped BigOperators
open SpanningHallLinearTools

theorem multilinear_zero_on_spans {I K V W : Type*} [Fintype I]
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {J : I → Type*} [∀i,Fintype (J i)]
    (a : ∀i,J i → V) (F : MultilinearMap K (fun _:I => V) W)
    (hF : ∀j:∀i,J i,F (fun i => a i (j i))=0)
    (v:I→V) (hv:∀i,v i∈Submodule.span K (Set.range (a i))) : F v=0 := by
  classical
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (hv i)
  have he : v=(fun i => ∑j,c i j • a i j) := (funext hc).symm
  rw [he,F.map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [F.map_smul_univ,hF,smul_zero]

theorem determinant_nonzero_of_independent {I K : Type*} [Fintype I]
    [DecidableEq I] [Field K] (v:Matrix I I K) (hv:LinearIndependent K v) :
    Matrix.det v≠0 := by
  have hi : Function.Injective (Matrix.transpose v).mulVec := by
    apply Matrix.mulVec_injective_iff.mpr
    change LinearIndependent K v
    exact hv
  obtain ⟨C,hC⟩ := SpanningFiniteFieldTransfer.matrix_left_inverse (Matrix.transpose v) hi
  have he := congrArg Matrix.det hC
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at he
  intro hz
  rw [hz,mul_zero] at he
  exact zero_ne_one he

theorem obstruction_of_mixed_determinants {I K : Type*} [Fintype I]
    [DecidableEq I] [Field K] {J:I→Type*} [∀i,Fintype (J i)]
    (a:∀i,J i→I→K)
    (ha:∀j:∀i,J i,Matrix.det (fun i => a i (j i))=0) :
    ∃s:Finset I,s.Nonempty ∧
      Module.finrank K (familySpan (fun i => Submodule.span K (Set.range (a i))) s)
        <s.card := by
  classical
  apply SpanningLinearHall.exists_obstruction
  intro v hv hi
  have hz := multilinear_zero_on_spans a Matrix.detRowAlternating.toMultilinearMap ha v hv
  exact determinant_nonzero_of_independent v hi hz

#print axioms obstruction_of_mixed_determinants

end SpanningMixedDeterminants
