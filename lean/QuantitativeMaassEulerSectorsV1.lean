module

public import QuantitativeMaassEulerComplexPhysicalV1
public import AsymptoticSectorSignsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter AsymptoticSectorSigns
open scoped Topology

namespace QuantitativeMaass

/-- All infinitely many local twist roots of original Euler data belong to
one of the finite sign sectors determined solely by the level. -/
theorem euler_root_sector {N : ℕ} {b : ℕ → ℂ}
    (hb : FinitenessOriginalInput.EulerData N b) (η : ℂ) (hη : η=1 ∨ η= -1) :
    ∃ e : Sector N,(∀ p,p∈simplePrimes N → delta e p=b p*(Real.sqrt p:ℂ)) ∧
      ∀ q,multiplier e q=η*FinitenessNormalizedTwistProduct.root N b q := by
  classical
  let e : Sector N := ⟨decide (η=1),fun p => decide (b p.val*(Real.sqrt p.val:ℂ)=1)⟩
  have hd (p : ℕ) (hp : p∈simplePrimes N) : delta e p=b p*(Real.sqrt p:ℂ) := by
    obtain ⟨hp',hpN,hpsq⟩ := mem_simplePrimes.mp hp
    simp only [delta,dite_eq_left hp,e]
    exact sign_decide (AsymptoticRamifiedCoefficients.simple_sign hb hp' hpN hpsq)
  refine ⟨e,hd,?_⟩
  intro q
  rw [multiplier,AsymptoticRamifiedCoefficients.twist_root]
  have hprod : (∏ p ∈ q.primeFactors.filter (fun p => p∣N ∧ ¬p^2∣N),-delta e p)=
      ∏ p ∈ q.primeFactors.filter (fun p => p∣N ∧ ¬p^2∣N),-(b p*(Real.sqrt p:ℂ)) := by
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨hpq,hpN,hpsq⟩ := Finset.mem_filter.mp hp
    rw [hd p (mem_simplePrimes.mpr ⟨Nat.prime_of_mem_primeFactors hpq,hpN,hpsq⟩)]
  rw [hprod,show sign e.1=η from sign_decide hη]

/-- A single finite root sector supplies every original Maass physical
functional equation, including ramified and identically zero twists. -/
theorem principalEulerPhysical_sector {N : ℕ} {b : ℕ → ℂ} (hN : 0<N)
    (r : ℝ) (σ : ℕ) (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ e : Sector N,(∀ p,p∈simplePrimes N → delta e p=b p*(Real.sqrt p:ℂ)) ∧
      ∀ q : ℕ,0<q → ∀ z : ℂ,0<z.im →
        FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q z=
          multiplier e q*FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q
            (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  obtain ⟨ε,hε,he⟩ := principal_original_ramanujan_reflections hN r σ hb
  have hη : (-1:ℂ)^σ*ε=1 ∨ (-1:ℂ)^σ*ε= -1 := by
    apply sq_eq_one_iff.mp
    rw [mul_pow,pow_right_comm,show ε^2=1 from sq_eq_one_iff.mpr hε]
    norm_num
  obtain ⟨e,hd,hm⟩ := euler_root_sector hb.toEulerData ((-1:ℂ)^σ*ε) hη
  refine ⟨e,hd,?_⟩
  intro q hq z hz
  have hL : (0:ℝ)<(Nat.lcm N (q^2):ℝ) := by exact_mod_cast Nat.lcm_pos hN (pow_pos hq 2)
  rw [principalEulerPhysical_twist,principalEulerPhysical_twist]
  rw [show (Nat.lcm N (q^2):ℂ)=((Nat.lcm N (q^2):ℝ):ℂ) by simp,
    fricke_complex_coordinates _ hL z hz,hm]
  have hh := he q hq z.re z.im hz
  convert hh using 1
  ring

#print axioms euler_root_sector
#print axioms principalEulerPhysical_sector

end QuantitativeMaass
