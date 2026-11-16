module

public import QuantitativeMaassSectorTwistArithmeticV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticFreshMatrices AsymptoticCongruenceStrip
open AsymptoticClassicalPetersson AsymptoticSectorSigns AsymptoticOrbitDecode

namespace QuantitativeMaass

/-- Modularity, Fricke and the local new ramified equations imply all
primitive twist laws in one fixed sector, including mixed composite moduli. -/
theorem modular_ramified_all_analytic_laws (N : ℕ) (hN : 0<N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) (e : Sector N)
    (hW : ∀ z,sign e.1*f.val (frickeLabel N hN • z)=f.val z)
    (hS : ∀ p : ℕ,∀ hp : p.Prime,p∣N → ¬p^2∣N → ∀ z : ℍ,
      ∑ a : Fin p,f.val (ramifiedLabel p hp.pos a • z)=delta e p*f.val z)
    (hR : ∀ p : ℕ,∀ hp : p.Prime,p^2∣N → ∀ z : ℍ,
      ∑ a : Fin p,f.val (ramifiedLabel p hp.pos a • z)=0) :
    ∀ q : ℕ,0<q → ∀ z : ℂ,
      FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) q z=
        multiplier e q*FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) q
          (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  have hper := upperZeroExtension_periodic N f
  have huS (p : ℕ) (hp : p.Prime) (hpN : p∣N) (hp2 : ¬p^2∣N) (z : ℂ) :
      ramifiedAverage p (upperZeroExtension f.val) z=delta e p*upperZeroExtension f.val z :=
    upperZeroExtension_ramified p hp.pos f.val (delta e p) (hS p hp hpN hp2) z
  have huR (p : ℕ) (hp : p.Prime) (hp2 : p^2∣N) (z : ℂ) :
      ramifiedAverage p (upperZeroExtension f.val) z=0 := by
    simpa only [zero_mul] using upperZeroExtension_ramified p hp.pos f.val 0
      (fun y => by simpa only [zero_mul] using hR p hp hp2 y) z
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq
    by_cases hc : N.Coprime q
    · intro z
      rw [multiplier_coprime e hc]
      exact (upperZeroExtension_coprime_law N q hN hq hc f (sign e.1) hW z).symm
    · obtain ⟨p,hp,hpN,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      obtain ⟨a,k,ha,hlt,hpa,hqa⟩ := ramified_prime_power_split q p hq hp hpq
      have hw (z : ℂ) : multiplier e a*
          FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) a
            (-1/((Nat.lcm N (a^2):ℂ)*z))=
          FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) a z :=
        (ih a hlt ha z).symm
      rw [hqa]
      by_cases hp2 : p^2∣N
      · have hm : multiplier e (a*p^(k+1))=multiplier e a := by
          rw [multiplier_prime_power_mul e a p ha hp hpa k,ite_eq_right]
          exact fun h => h.2 hp2
        intro z
        rw [hm]
        exact analytic_twist_repeated_extension N p a hp ha hpa hp2 k
          (upperZeroExtension f.val) hper (multiplier e a) (huR p hp hp2) hw z
      · obtain ⟨M,hM,hcM,hL⟩ := simple_lcm_factor N a p hN ha hp hpN hp2 hpa
        have hm : -multiplier e a*delta e p=multiplier e (a*p^(k+1)) := by
          rw [multiplier_prime_power_mul e a p ha hp hpa k,ite_eq_left ⟨hpN,hp2⟩]
          ring
        intro z
        by_cases hz : z=0
        · subst z
          simp only [mul_zero,div_zero]
          rw [upperZeroExtension_twist_zero f.val _ 0 (by simp),mul_zero]
        · have he := analytic_twist_simple_extension N M p a hM hp ha hcM hpa hL k
            (upperZeroExtension f.val) hper (multiplier e a) (delta e p) (delta_sq e p)
            (huS p hp hpN hp2) hw z hz
          rw [hm] at he
          exact he

#print axioms modular_ramified_all_analytic_laws

end QuantitativeMaass
