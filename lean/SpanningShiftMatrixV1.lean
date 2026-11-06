module

public import SpanningPolynomialDeterminantsV1
public import SpanningSpectralTracesV1

@[expose] public section

namespace SpanningShiftMatrix

open scoped BigOperators
open SpanningSpectralCoordinates SpanningPolynomialShift SpanningTraceAlgebra Matrix Polynomial

variable {K I:Type*} [Field K] [Fintype I] [DecidableEq I] {Q:ℕ}

omit [DecidableEq I] in
theorem exponential_sum (z:Fin Q→K) (a:I→Fin Q→K) :
    (∑i,exponentialWord z (a i))=exponentialWord z (fun k => ∑i,a i k) := by
  funext n
  simp only [Finset.sum_apply,exponentialWord,Finset.sum_mul]
  exact Finset.sum_comm

theorem determinant_annihilates {z:Fin Q→K} (hQ:0<Q)
    (hi:Function.Injective z) (hz0:∀i,z i≠0) (hzQ:∀i,z i^Q=1)
    (F:Matrix I I K[X]) (u:ℕ) (f:I→ℤ→K) (hf:∀i,Cyclic Q (f i))
    (hrel:∀j,(∑i,shiftPolynomial (F j i) u (f i))=0) :
    ∀i,shiftPolynomial F.det u (f i)=0 := by
  classical
  choose a ha using fun i => (exponential_expansion hQ hi hz0 hzQ (f i) (hf i)).exists
  have hcoeff : ∀j k,∑i,a i k*(F j i).eval (z k^u)=0 := by
    intro j
    have he := hrel j
    simp_rw [←ha,shift_exponential hz0] at he
    rw [exponential_sum] at he
    have he' : exponentialWord z (fun k => ∑i,a i k*(F j i).eval (z k^u))=
        exponentialWord z 0 := by
      rw [he]
      funext n
      simp [exponentialWord]
    exact fun k => congrFun (exponentialWord_injective hi he') k
  have hdet : ∀i k,a i k*F.det.eval (z k^u)=0 := by
    intro i k
    let E : Matrix I I K := F.map (evalRingHom (z k^u))
    have he : E.mulVec (fun i => a i k)=0 := by
      funext j
      change (∑i,(F j i).eval (z k^u)*a i k)=0
      simpa only [mul_comm] using hcoeff j k
    have hh := congrArg (fun v => E.adjugate.mulVec v) he
    rw [mulVec_mulVec,adjugate_mul,smul_mulVec,one_mulVec,mulVec_zero] at hh
    have hv := congrFun hh i
    change E.det*a i k=0 at hv
    have hd := RingHom.map_det (evalRingHom (z k^u)) F
    change F.det.eval (z k^u)=E.det at hd
    rw [←hd,mul_comm] at hv
    exact hv
  intro i
  rw [←ha i,shift_exponential hz0]
  have he : (fun k => a i k*F.det.eval (z k^u))=0 := funext (hdet i)
  rw [he]
  funext n
  simp [exponentialWord]

theorem determinant_zero_of_short_relation {ζ:K} (hQ:0<Q)
    (hζ:IsPrimitiveRoot ζ Q) (F:Matrix I I K[X]) (u:ℕ) (hu:Nat.Coprime u Q)
    (f:I→ℤ→K) (hf:∀i,Cyclic Q (f i))
    (hrel:∀j,(∑i,shiftPolynomial (F j i) u (f i))=0)
    (i:I) (hfi:f i≠0) (L:ℕ) (hzero:∀j:ℕ,j<L→f i j=0)
    (hdeg:F.det.natDegree≤L) : F.det=0 := by
  let z := fun k:Fin Q => ζ^k.val
  have hi : Function.Injective z := fun i j he => Fin.ext (hζ.pow_inj i.isLt j.isLt he)
  have hz0 : ∀k,z k≠0 := fun k => pow_ne_zero _ (hζ.ne_zero (Nat.ne_of_gt hQ))
  have hzQ : ∀k,z k^Q=1 := by
    intro k
    dsimp [z]
    rw [←pow_mul,mul_comm k.val Q,pow_mul,hζ.pow_eq_one,one_pow]
  exact no_small_shift_annihilator hQ hζ u hu (f i) (hf i) hfi hzero F.det hdeg
    (determinant_annihilates hQ hi hz0 hzQ F u f hf hrel i)

#print axioms determinant_zero_of_short_relation

end SpanningShiftMatrix
