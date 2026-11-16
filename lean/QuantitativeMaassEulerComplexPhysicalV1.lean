module

public import QuantitativeMaassRamanujanWaveV1
public import FinitenessGlobalHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass

/-- Complex coordinates for the actual real-analytic wave, not a holomorphic
function of the physical upper half-plane variable. -/
def principalEulerPhysical (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (z : ℂ) : ℂ :=
  principalEulerWave b r σ (z.re,z.im)

theorem principalEulerPhysical_periodic (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (z : ℂ) :
    principalEulerPhysical b r σ (z+1)=principalEulerPhysical b r σ z := by
  simpa [principalEulerPhysical] using principalEulerWave_periodic b r σ z.im z.re

theorem principalEulerPhysical_twist (b : ℕ → ℂ) (r : ℝ) (σ q : ℕ) (z : ℂ) :
    FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q z=
      principalRamanujanWave b r σ q (z.re,z.im) := by
  unfold FinitenessAnalyticReconstruction.twist principalRamanujanWave FinitenessRamanujanSum.residues
  apply Finset.sum_congr rfl
  intro a _
  simp [principalEulerPhysical,←Complex.ofReal_natCast,←Complex.ofReal_div]

theorem fricke_complex_coordinates (L : ℝ) (hL : 0<L) (z : ℂ) (hz : 0<z.im) :
    ((-1/((L:ℂ)*z)).re,(-1/((L:ℂ)*z)).im)=MaassDifferential.F L z.re z.im := by
  have hn : z.re^2+z.im^2≠0 := ne_of_gt (by nlinarith [sq_nonneg z.re])
  apply Prod.ext
  · simp only [neg_div,one_div,Complex.neg_re,Complex.inv_re,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,
      Complex.normSq_apply,MaassDifferential.F]
    field_simp
  · exact FinitenessComplexGeometry.reflected_im hL hz

/-- Original Euler data supplies the exact weight-zero twisted laws required
by the strict certificate reconstruction machinery. -/
theorem principalEulerPhysical_original_FE {N : ℕ} {b : ℕ → ℂ} (hN : 0<N)
    (r : ℝ) (σ : ℕ) (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ χ : ℕ → ℂ,(∀ q,‖χ q‖=1) ∧ ∀ q : ℕ,0<q → ∀ z : ℂ,0<z.im →
      FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q z=
        χ q*FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q
          (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  obtain ⟨ε,hε,he⟩ := principal_original_ramanujan_reflections hN r σ hb
  refine ⟨fun q => (-1:ℂ)^σ*(FinitenessNormalizedTwistProduct.root N b q*ε),?_,?_⟩
  · intro q
    rcases FinitenessNormalizedTwistProduct.root_unit hb.toEulerData q with hq|hq <;>
      rcases hε with hε|hε <;> simp [hq,hε,norm_pow]
  · intro q hq z hz
    have hL : (0:ℝ)<(Nat.lcm N (q^2):ℝ) := by exact_mod_cast Nat.lcm_pos hN (pow_pos hq 2)
    rw [principalEulerPhysical_twist,principalEulerPhysical_twist]
    rw [show (Nat.lcm N (q^2):ℂ)=((Nat.lcm N (q^2):ℝ):ℂ) by simp,
      fricke_complex_coordinates _ hL z hz]
    exact he q hq z.re z.im hz

#print axioms principalEulerPhysical_periodic
#print axioms principalEulerPhysical_twist
#print axioms fricke_complex_coordinates
#print axioms principalEulerPhysical_original_FE

end QuantitativeMaass
