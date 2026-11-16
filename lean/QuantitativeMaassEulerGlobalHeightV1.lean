module

public import QuantitativeMaassEulerComplexPhysicalV1
public import QuantitativeMaassEulerHeightEnvelopeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass

/-- A strict rational certificate and the literal original Euler hypotheses
give one global height exponent fixed before the coefficients and parameter.
No global boundedness or automorphy premise is used. -/
theorem principalEulerPhysical_global_height {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ C : ℝ,0≤C ∧ ∀ z : ℂ,0<z.im → z.im^P.s*‖principalEulerPhysical b r σ z‖≤C := by
  let F := principalEulerPhysical b r σ
  let V : ℂ → ℝ := fun z => z.im^P.s*‖F z‖
  let E := FinitenessHeightEnvelope.envelope Complex.im V
  have hne : ∀ y : ℝ,0<y → (FinitenessHeightEnvelope.tailSet Complex.im V y).Nonempty := by
    intro y _
    refine ⟨V (y*Complex.I),y*Complex.I,?_,rfl⟩
    simp
  have hbd : ∀ y : ℝ,0<y → BddAbove (FinitenessHeightEnvelope.tailSet Complex.im V y) := by
    intro y hy
    obtain ⟨C,_,hC⟩ := principalEulerWave_height_bound hb.polynomialGrowth r σ P.s y hy
    refine ⟨C,?_⟩
    rintro v ⟨z,hz,rfl⟩
    exact hC z.re z.im hz
  have hE : ∀ y : ℝ,0<y → 0≤E y := by
    intro y hy
    have hm : V (y*Complex.I)∈FinitenessHeightEnvelope.tailSet Complex.im V y :=
      ⟨y*Complex.I,by simp,rfl⟩
    have hv : 0≤V (y*Complex.I) := by dsimp [V]; simp only [Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.ofReal_im,Complex.I_re,mul_one,mul_zero,add_zero]; positivity
    exact hv.trans (le_csSup (hbd y hy) hm)
  obtain ⟨χ,hχ,hFE⟩ := principalEulerPhysical_original_FE hN r σ hb
  have hr : 1<P.ρ⁻¹ := (one_lt_inv₀ P.rho_pos).mpr P.rho_lt_one
  have hpoint : ∀ z : ℂ,0<z.im → z.im<P.ε → V z≤E (P.ρ⁻¹*z.im) := by
    intro z hz hze
    have hh := FinitenessGlobalHeight.pointwise hN A P F
      (principalEulerPhysical_periodic b r σ) χ 0 (fun q _ => hχ q)
      (fun q hq w hw => by
        simpa only [mul_zero,pow_zero,div_one] using hFE q (Nat.pos_of_dvd_of_pos hq hQ) w hw)
      z hz hze.le (hE _ (mul_pos (inv_pos.mpr P.rho_pos) hz)) (by
        intro w hw
        apply le_csSup (hbd _ (mul_pos (inv_pos.mpr P.rho_pos) hz))
        refine ⟨w,?_,?_⟩
        · simpa only [div_eq_mul_inv,mul_comm] using hw
        · simp only [zero_add];rfl)
    simpa only [zero_add] using hh
  refine ⟨E P.ε,hE P.ε P.epsilon_pos,?_⟩
  intro z hz
  exact FinitenessHeightEnvelope.pointwise_global_bound Complex.im V
    P.epsilon_pos hr hne hbd hpoint z hz

#print axioms principalEulerPhysical_global_height

end QuantitativeMaass
