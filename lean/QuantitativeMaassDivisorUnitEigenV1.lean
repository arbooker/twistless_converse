module

public import QuantitativeMaassDivisorCharacterV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson
namespace QuantitativeMaass

/-- Having a unit eigenvalue depends only on the actual quotient action. -/
theorem generator_unitEigen_congr (N : ℕ) (hN : 0<N) (x : AutomorphicSpace N)
    (Q : ℕ) (i j : admissibleGeneratorIndex N hN)
    (hi : generatorAtDivisor N hN Q i) (hj : generatorAtDivisor N hN Q j) :
    admissibleGeneratorLift N hN i∈normalizerEigenStabilizer N x ↔
      admissibleGeneratorLift N hN j∈normalizerEigenStabilizer N x := by
  change (∃ c : ℂ,‖c‖=1 ∧ quotientNormalizerPullback N (admissibleGeneratorLift N hN i) x=c • x) ↔
    (∃ c : ℂ,‖c‖=1 ∧ quotientNormalizerPullback N (admissibleGeneratorLift N hN j) x=c • x)
  rw [generatorAtDivisor_action_eq N hN Q i j hi hj]

#print axioms generator_unitEigen_congr

/-- The exact-divisor product identity holds inside the actual unit-eigenvalue
stabilizer, allowing both multiplication and cancellation of factors. -/
theorem generator_product_unitEigen_iff (N : ℕ) (hN : 0<N) (x : AutomorphicSpace N)
    (D P Q : ℕ) (hP : 0<P) (hQ : 0<Q) (hND : (P*Q)*D=N)
    (A B C E U V : ℤ)
    (hAB : (P:ℤ)*A+((Q*D:ℕ):ℤ)*B=1)
    (hCE : (Q:ℤ)*C+((P*D:ℕ):ℤ)*E=1)
    (hUV : ((P*Q:ℕ):ℤ)*U+(D:ℤ)*V=1)
    (i j k : admissibleGeneratorIndex N hN)
    (hi : i.val=exactAtkinLabel (Q*D) P hP A B hAB)
    (hj : j.val=exactAtkinLabel (P*D) Q hQ C E hCE)
    (hk : k.val=exactAtkinLabel D (P*Q) (Nat.mul_pos hP hQ) U V hUV) :
    admissibleGeneratorLift _ hN i*admissibleGeneratorLift _ hN j∈normalizerEigenStabilizer _ x ↔
      admissibleGeneratorLift _ hN k∈normalizerEigenStabilizer _ x := by
  obtain ⟨a,ha⟩ := exactAtkin_product_mod_gamma D P Q hP hQ A B C E U V hAB hCE hUV
  let aN : AsymptoticCongruenceStrip.gamma N := ⟨a.val,by simpa only [hND] using a.property⟩
  have he := quotientNormalizerPullback_left_gamma N
    (admissibleGeneratorLift _ hN i*admissibleGeneratorLift _ hN j)
    (admissibleGeneratorLift _ hN k) aN (by
      change i.val*j.val=a.val*k.val
      rw [hi,hj,hk]
      exact ha) x
  change (∃ c : ℂ,‖c‖=1 ∧ _=c • x) ↔ (∃ c : ℂ,‖c‖=1 ∧ _=c • x)
  rw [he]

#print axioms generator_product_unitEigen_iff

def divisorUnitEigen (N : ℕ) (hN : 0<N) (x : AutomorphicSpace N) (Q : ℕ) : Prop :=
  ∀ i : admissibleGeneratorIndex N hN,generatorAtDivisor N hN Q i →
    admissibleGeneratorLift N hN i∈normalizerEigenStabilizer N x

theorem divisorUnitEigen_mul (N : ℕ) (hN : 0<N) (x : AutomorphicSpace N)
    (P Q D : ℕ) (hP : 0<P) (hQ : 0<Q) (hPQ : Nat.Coprime P Q)
    (hcop : Nat.Coprime (P*Q) D) (hND : (P*Q)*D=N)
    (hp : divisorUnitEigen N hN x P) (hq : divisorUnitEigen N hN x Q) :
    divisorUnitEigen N hN x (P*Q) := by
  have hpc := hPQ.mul_right (hcop.of_dvd_left (dvd_mul_right P Q))
  have hqc := hPQ.symm.mul_right (hcop.of_dvd_left (dvd_mul_left Q P))
  let i := exactDivisorGeneratorIndex _ hN P (Q*D) hP hpc (by nlinarith [hND])
  let j := exactDivisorGeneratorIndex _ hN Q (P*D) hQ hqc (by nlinarith [hND])
  let k := exactDivisorGeneratorIndex _ hN (P*Q) D (Nat.mul_pos hP hQ) hcop hND
  have hi := hp i ⟨Q*D,hP,_,_,_,by nlinarith [hND],rfl⟩
  have hj := hq j ⟨P*D,hQ,_,_,_,by nlinarith [hND],rfl⟩
  have hk := (generator_product_unitEigen_iff N hN x D P Q hP hQ hND
    _ _ _ _ _ _ _ _ _ i j k rfl rfl rfl).mp
      ((normalizerEigenStabilizer _ x).mul_mem hi hj)
  intro l hl
  exact (generator_unitEigen_congr _ hN x (P*Q) k l
    ⟨D,Nat.mul_pos hP hQ,_,_,_,hND,rfl⟩ hl).mp hk

#print axioms divisorUnitEigen_mul

theorem divisorUnitEigen_cancel (N : ℕ) (hN : 0<N) (x : AutomorphicSpace N)
    (P Q : ℕ) (hP : 0<P) (hQ : 0<Q) (hPQ : Nat.Coprime P Q) (hNQ : P*Q=N)
    (hn : divisorUnitEigen N hN x N) (hq : divisorUnitEigen N hN x Q) :
    divisorUnitEigen N hN x P := by
  have hND : (P*Q)*1=N := by simpa only [Nat.mul_one] using hNQ
  let i := exactDivisorGeneratorIndex N hN P (Q*1) hP
    (by simpa only [Nat.mul_one] using hPQ) (by nlinarith [hNQ])
  let j := exactDivisorGeneratorIndex N hN Q (P*1) hQ
    (by simpa only [Nat.mul_one] using hPQ.symm) (by nlinarith [hNQ])
  let k := exactDivisorGeneratorIndex N hN (P*Q) 1 (Nat.mul_pos hP hQ)
    (Nat.coprime_one_right _) hND
  have hk : admissibleGeneratorLift N hN k∈normalizerEigenStabilizer N x := by
    apply hn k
    have hki : generatorAtDivisor N hN (P*Q) k := ⟨1,Nat.mul_pos hP hQ,_,_,_,hND,rfl⟩
    exact Eq.mp (congrArg (fun R => generatorAtDivisor N hN R k) hNQ) hki
  have hj := hq j ⟨P*1,hQ,_,_,_,by nlinarith [hNQ],rfl⟩
  have hm := (generator_product_unitEigen_iff N hN x 1 P Q hP hQ hND
    _ _ _ _ _ _ _ _ _ i j k rfl rfl rfl).mpr hk
  have hi := (normalizerEigenStabilizer N x).mul_mem hm ((normalizerEigenStabilizer N x).inv_mem hj)
  rw [mul_inv_cancel_right] at hi
  intro l hl
  exact (generator_unitEigen_congr N hN x P i l ⟨Q*1,hP,_,_,_,by nlinarith [hNQ],rfl⟩ hl).mp hi

#print axioms divisorUnitEigen_cancel
end QuantitativeMaass
