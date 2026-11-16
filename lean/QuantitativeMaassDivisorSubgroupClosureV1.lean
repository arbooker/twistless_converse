module
public import QuantitativeMaassExactDivisorSubgroupV1
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticSectorSigns AsymptoticFreshMatrices
namespace QuantitativeMaass.CountingMetric
variable (N : ℕ) (hN : 0<N) (K : Subgroup AsymptoticRationalGroup.Group) (hK : gamma N≤K)
include hK
theorem divisorMem_mul (P Q D : ℕ) (hP : 0<P) (hQ : 0<Q) (hPQ : Nat.Coprime P Q)
    (hcop : Nat.Coprime (P*Q) D) (hND : (P*Q)*D=N)
    (hp : divisorMem N hN K P) (hq : divisorMem N hN K Q) : divisorMem N hN K (P*Q) := by
  have hpc := hPQ.mul_right (hcop.of_dvd_left (dvd_mul_right P Q))
  have hqc := hPQ.symm.mul_right (hcop.of_dvd_left (dvd_mul_left Q P))
  let i := exactDivisorGeneratorIndex _ hN P (Q*D) hP hpc (by nlinarith [hND])
  let j := exactDivisorGeneratorIndex _ hN Q (P*D) hQ hqc (by nlinarith [hND])
  let k := exactDivisorGeneratorIndex _ hN (P*Q) D (Nat.mul_pos hP hQ) hcop hND
  have hi := hp i ⟨Q*D,hP,_,_,_,by nlinarith [hND],rfl⟩
  have hj := hq j ⟨P*D,hQ,_,_,_,by nlinarith [hND],rfl⟩
  have hk := (generator_product_mem_iff N hN K hK D P Q hP hQ hND
    _ _ _ _ _ _ _ _ _ i j k rfl rfl rfl).mp (K.mul_mem hi hj)
  intro l hl
  exact (generator_mem_congr N hN K hK (P*Q) k l
    ⟨D,Nat.mul_pos hP hQ,_,_,_,hND,rfl⟩ hl).mp hk

theorem divisorMem_cancel (P Q : ℕ) (hP : 0<P) (hQ : 0<Q)
    (hPQ : Nat.Coprime P Q) (hNQ : P*Q=N)
    (hn : divisorMem N hN K N) (hq : divisorMem N hN K Q) : divisorMem N hN K P := by
  have hND : (P*Q)*1=N := by simpa only [Nat.mul_one] using hNQ
  let i := exactDivisorGeneratorIndex N hN P (Q*1) hP
    (by simpa only [Nat.mul_one] using hPQ) (by nlinarith [hNQ])
  let j := exactDivisorGeneratorIndex N hN Q (P*1) hQ
    (by simpa only [Nat.mul_one] using hPQ.symm) (by nlinarith [hNQ])
  let k := exactDivisorGeneratorIndex N hN (P*Q) 1 (Nat.mul_pos hP hQ)
    (Nat.coprime_one_right _) hND
  have hk : k.val∈K := by
    apply hn k
    have hki : generatorAtDivisor N hN (P*Q) k := ⟨1,Nat.mul_pos hP hQ,_,_,_,hND,rfl⟩
    exact Eq.mp (congrArg (fun R => generatorAtDivisor N hN R k) hNQ) hki
  have hj := hq j ⟨P*1,hQ,_,_,_,by nlinarith [hNQ],rfl⟩
  have hm := (generator_product_mem_iff N hN K hK 1 P Q hP hQ hND
    _ _ _ _ _ _ _ _ _ i j k rfl rfl rfl).mpr hk
  have hi := K.mul_mem hm (K.inv_mem hj)
  rw [mul_inv_cancel_right] at hi
  intro l hl
  exact (generator_mem_congr N hN K hK P i l ⟨Q*1,hP,_,_,_,by nlinarith [hNQ],rfl⟩ hl).mp hi


#print axioms divisorMem_mul
#print axioms divisorMem_cancel
end QuantitativeMaass.CountingMetric
