module

public import QuantitativeMaassPrimePowerTwistsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- The conductor of a prime-power twist at a prime occurring once. -/
theorem simple_prime_power_lcm (M p k : ℕ) (hc : M.Coprime p) :
    Nat.lcm (p*M) ((p^(k+1))^2)=M*(p^(k+1))^2 := by
  have hd : p∣(p^(k+1))^2 := by
    apply (dvd_pow_self p (by omega : k+1≠0)).trans
    exact dvd_pow_self _ (by decide : 2≠0)
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · simpa only [Nat.mul_comm p M] using Nat.mul_dvd_mul_left M hd
    · exact Nat.dvd_mul_left _ _
  · exact ((hc.pow_right (k+1)).pow_right 2).mul_dvd_of_dvd_of_dvd
      ((Nat.dvd_mul_left M p).trans (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _)

/-- Iterating the actual U_p equation gives the full primitive reflection
law at every power of a simply ramified prime. -/
theorem simple_prime_power_analytic_law (M p : ℕ) (hM : 0<M) (hp : p.Prime)
    (hc : M.Coprime p) (k : ℕ) (F : ℂ → ℂ) (w δ : ℂ) (hδ : δ^2=1)
    (hU : ∀ z,ramifiedAverage p F z=δ*F z)
    (hW : ∀ z : ℂ,w*F (-1/(((p*M:ℕ):ℂ)*z))=F z)
    (z : ℂ) (hz : z≠0) :
    FinitenessAnalyticReconstruction.twist F (p^(k+1)) z=
      (-w*δ)*FinitenessAnalyticReconstruction.twist F (p^(k+1))
        (-1/((Nat.lcm (p*M) ((p^(k+1))^2):ℂ)*z)) := by
  rw [simple_prime_power_lcm M p k hc]
  let L : ℂ := (M*(p^(k+1))^2:ℕ)
  let A : ℂ := (p^(k+1):ℕ)
  let B : ℂ := (p^k:ℕ)
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
  have hM0 : (M:ℂ)≠0 := by exact_mod_cast hM.ne'
  have hB : B≠0 := by dsimp only [B]; exact_mod_cast (pow_pos hp.pos k).ne'
  have hA : A=(p:ℂ)*B := by simp only [A,B,pow_succ',Nat.cast_pow]
  have hL : L=(M:ℂ)*A^2 := by simp only [L,A,Nat.cast_mul,Nat.cast_pow]
  have h₁ : A*(-1/(L*z))= -1/(((p*M:ℕ):ℂ)*(B*z)) := by
    rw [hL,hA,Nat.cast_mul]
    field_simp
  have h₂ : B*(-1/(L*z))= -1/(((p*M:ℕ):ℂ)*(A*z)) := by
    rw [hL,hA,Nat.cast_mul]
    field_simp
  have hw₁ : w*F (A*(-1/(L*z)))=F (B*z) := by rw [h₁]; exact hW _
  have hw₂ : w*F (B*(-1/(L*z)))=F (A*z) := by rw [h₂]; exact hW _
  have hd : δ^(k+2)=δ^k := by rw [pow_add,hδ,mul_one]
  rw [analytic_twist_prime_power_of_ramified p hp k F δ hU,
    analytic_twist_prime_power_of_ramified p hp k F δ hU]
  change δ^(k+1)*F (A*z)-δ^k*F (B*z)=
    (-w*δ)*(δ^(k+1)*F (A*(-1/(L*z)))-δ^k*F (B*(-1/(L*z))))
  calc
    _ = δ^(k+1)*(w*F (B*(-1/(L*z))))-δ^(k+2)*(w*F (A*(-1/(L*z)))) := by
      rw [hw₁,hw₂,hd]
    _ = _ := by rw [show k+2=(k+1)+1 by omega,pow_succ,pow_succ]; ring

#print axioms simple_prime_power_lcm
#print axioms simple_prime_power_analytic_law

end QuantitativeMaass
