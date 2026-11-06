module

public import SpanningPolynomialShiftV1
public import SpanningActualKernelV1
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

namespace SpanningSpectralTraces

open SpanningSpectralCoordinates SpanningPolynomialShift SpanningTraceAlgebra
  SpanningActualKernel SpanningWindows SpanningVandermonde

variable {K:Type*} [Field K] {Q:ℕ}

theorem trace_exponential {z:Fin Q → K} (hz0:∀i,z i≠0)
    (a:Fin Q → K) (q B:ℕ) :
    trace q B (exponentialWord z a)=
      exponentialWord z (fun i => a i*∑t∈Finset.range q,(z i^B)^t) := by
  funext n
  unfold trace exponentialWord
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [zpow_add₀ (hz0 i),zpow_mul,zpow_natCast,zpow_natCast]
  rw [←pow_mul,←pow_mul,Nat.mul_comm t B]
  ring

theorem zero_trace_coefficients {z:Fin Q → K} (hi:Function.Injective z)
    (hz0:∀i,z i≠0) {a:Fin Q → K} {q B:ℕ}
    (ht:trace q B (exponentialWord z a)=0) :
    ∀i,a i*(∑t∈Finset.range q,(z i^B)^t)=0 := by
  rw [trace_exponential hz0] at ht
  have he : exponentialWord z (fun i => a i*∑t∈Finset.range q,(z i^B)^t)=
      exponentialWord z 0 := by
    rw [ht]
    funext n
    simp [exponentialWord]
  exact fun i => congrFun (exponentialWord_injective hi he) i

theorem coefficient_zero_of_trace [CharZero K] {ζ:K} (hQ:0<Q)
    (hζ:IsPrimitiveRoot ζ Q) {a:Fin Q → K} {q:ℕ} (hq:q∣Q)
    (ht:trace q (Q/q) (exponentialWord (fun i:Fin Q => ζ^i.val) a)=0)
    (i:Fin Q) (hqi:q∣i.val) : a i=0 := by
  have hqpos : 0<q := Nat.pos_of_dvd_of_pos hq hQ
  have hi : Function.Injective (fun i:Fin Q => ζ^i.val) :=
    fun i j he => Fin.ext (hζ.pow_inj i.isLt j.isLt he)
  have hnz : ∀i:Fin Q,ζ^i.val≠0 := fun i => pow_ne_zero _ (hζ.ne_zero (Nat.ne_of_gt hQ))
  have he := zero_trace_coefficients hi hnz ht i
  have hpow : (ζ^i.val)^(Q/q)=1 := by
    obtain ⟨k,hk⟩ := hqi
    rw [←pow_mul,hk]
    have hn : q*k*(Q/q)=Q*k := by
      calc q*k*(Q/q)=(q*(Q/q))*k := by ring
           _=Q*k := by rw [Nat.mul_div_cancel' hq]
    rw [hn,pow_mul,hζ.pow_eq_one,one_pow]
  simp only [hpow,one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at he
  exact (mul_eq_zero.mp he).resolve_right (by exact_mod_cast (Nat.ne_of_gt hqpos))

theorem complex_no_small_shift_annihilator {Q L:ℕ} (hQ:0<Q)
    (u:ℕ) (hu:Nat.Coprime u Q) (f:ℤ → ℂ) (hf:Cyclic Q f) (hf0:f≠0)
    (hz:∀j:ℕ,j<L → f j=0) (p:Polynomial ℂ) (hdeg:p.natDegree≤L)
    (hann:shiftPolynomial p u f=0) : p=0 :=
  no_small_shift_annihilator hQ (Complex.isPrimitiveRoot_exp Q (Nat.ne_of_gt hQ))
    u hu f hf hf0 hz p hdeg hann

#print axioms coefficient_zero_of_trace
#print axioms complex_no_small_shift_annihilator

end SpanningSpectralTraces
