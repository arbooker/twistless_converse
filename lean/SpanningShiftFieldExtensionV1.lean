module

public import SpanningShiftMatrixV1

@[expose] public section

namespace SpanningShiftFieldExtension

open scoped BigOperators
open Polynomial SpanningPolynomialShift SpanningTraceAlgebra

theorem map_shift {K K':Type*} [Field K] [Field K'] (σ:K→+*K')
    (p:K[X]) (u:ℕ) (f:ℤ→K) (n:ℤ) :
    shiftPolynomial (p.map σ) u (fun n => σ (f n)) n=σ (shiftPolynomial p u f n) := by
  unfold shiftPolynomial
  rw [Polynomial.support_map_of_injective p σ.injective]
  simp only [coeff_map,map_sum,map_mul]

theorem determinant_zero_over_extension {K K' I:Type*} [Field K] [Field K']
    [Fintype I] [DecidableEq I] {B:ℕ} {ζ:K'} (σ:K→+*K')
    (hB:0<B) (hζ:IsPrimitiveRoot ζ B) (F:Matrix I I K[X]) (u:ℕ) (hu:Nat.Coprime u B)
    (f:I→ℤ→K) (hf:∀i,Cyclic B (f i))
    (hrel:∀j,(∑i,shiftPolynomial (F j i) u (f i))=0)
    (i:I) (hfi:f i≠0) (L:ℕ) (hz:∀j:ℕ,j<L→f i j=0)
    (hdeg:F.det.natDegree≤L) : F.det=0 := by
  let F' : Matrix I I K'[X] := F.map (mapRingHom σ)
  let f' : I→ℤ→K' := fun i n => σ (f i n)
  have hrel' : ∀j,(∑i,shiftPolynomial (F' j i) u (f' i))=0 := by
    intro j
    funext n
    simp only [Finset.sum_apply,Pi.zero_apply]
    change (∑i,shiftPolynomial ((F j i).map σ) u (fun n => σ (f i n)) n)=0
    simp_rw [map_shift,←map_sum]
    have he := congrFun (hrel j) n
    simp only [Finset.sum_apply,Pi.zero_apply] at he
    rw [he,map_zero]
  have hd : F.det.map σ=F'.det := RingHom.map_det (mapRingHom σ) F
  have hzero : F'.det=0 := SpanningShiftMatrix.determinant_zero_of_short_relation hB hζ F' u hu
    f' (fun i n => congrArg σ (hf i n)) hrel' i (by
      intro he
      apply hfi
      funext n
      apply σ.injective
      exact (congrFun he n).trans (σ.map_zero).symm)
    L (fun j hj => by change σ (f i j)=0; rw [hz j hj,map_zero])
    (by rw [←hd]; exact natDegree_map_le.trans hdeg)
  exact (Polynomial.map_eq_zero_iff σ.injective).mp (hd.trans hzero)

#print axioms determinant_zero_over_extension

end SpanningShiftFieldExtension
