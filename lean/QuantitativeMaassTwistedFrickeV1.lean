module

public import QuantitativeMaassTwistContinuationV1
public import MaassEulerInputV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem euler_twisted_polynomialGrowth {N : ℕ} {b : ℕ → ℂ}
    (hb : FinitenessOriginalInput.EulerData N b) (q : ℕ) :
    MaassOriginal.PolynomialGrowth (FinitenessRamanujanFourier.twisted b q) := by
  obtain ⟨τ,_,hg⟩ := hb.growth
  exact ⟨τ,(FinitenessRamanujanFourier.twisted_growth hg q).norm_left⟩

/-- Every literal positive Ramanujan twist satisfies its global physical
Fricke equation, derived from the original Euler data and one untwisted root. -/
theorem principal_twisted_fricke {N : ℕ} {b : ℕ → ℂ} (hN : 0<N)
    (hb : FinitenessOriginalInput.EulerData N b) (r : ℝ) (σ : ℕ) (hσ : σ=0 ∨ σ=1)
    (ε : ℂ) (hε : ‖ε‖=1) (hcont : MaassOriginal.Continuation (N:ℝ) (.principal r) σ b ε)
    (q : ℕ) (hq : 0<q) :
    ∀ x y : ℝ,0<y → principalEulerWave (FinitenessRamanujanFourier.twisted b q) r σ (x,y)=
      ((-1:ℂ)^σ*(FinitenessNormalizedTwistProduct.root N b q*ε))*
        principalEulerWave (FinitenessRamanujanFourier.twisted b q) r σ
          (MaassDifferential.F (Nat.lcm N (q^2):ℝ) x y) := by
  have hL : (0:ℝ)<(Nat.lcm N (q^2):ℝ) := by exact_mod_cast Nat.lcm_pos hN (pow_pos hq 2)
  have hr : ‖FinitenessNormalizedTwistProduct.root N b q*ε‖=1 := by
    rcases FinitenessNormalizedTwistProduct.root_unit hb q with hh|hh <;> simp [hh,hε]
  exact principalEulerWave_fricke (euler_twisted_polynomialGrowth hb q) _ hL r σ hσ _ hr
    (maass_twisted_continuation hN hb (.principal r) σ ε hcont hq)

/-- One original Euler solution gives a coherent family of all positive twist
reflection laws, including ramified moduli and identically zero twists. -/
theorem principal_original_coherent_twist_reflections {N : ℕ} {b : ℕ → ℂ} (hN : 0<N)
    (r : ℝ) (σ : ℕ) (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ ε : ℂ,(ε=1 ∨ ε= -1) ∧ ∀ q : ℕ,0<q → ∀ x y : ℝ,0<y →
      principalEulerWave (FinitenessRamanujanFourier.twisted b q) r σ (x,y)=
        ((-1:ℂ)^σ*(FinitenessNormalizedTwistProduct.root N b q*ε))*
          principalEulerWave (FinitenessRamanujanFourier.twisted b q) r σ
            (MaassDifferential.F (Nat.lcm N (q^2):ℝ) x y) := by
  obtain ⟨ε,hε,hcont⟩ := hb.continuation
  refine ⟨ε,hε,?_⟩
  have hn : ‖ε‖=1 := by rcases hε with rfl|rfl <;> norm_num
  exact principal_twisted_fricke hN hb.toEulerData r σ hb.parity ε hn hcont

#print axioms euler_twisted_polynomialGrowth
#print axioms principal_twisted_fricke
#print axioms principal_original_coherent_twist_reflections

end QuantitativeMaass
