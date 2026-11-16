module

public import QuantitativeMaassWeightedStripL2V1
public import QuantitativeMaassEulerGlobalHeightV1
public import AsymptoticWeightedBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

theorem principalEulerPhysical_continuous_upper {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (r : ℝ) (σ : ℕ) :
    Continuous (fun z : ℍ => principalEulerPhysical b r σ z) :=
  (principalEulerWave_continuousOn hb r σ).comp_continuous
    (continuous_re.prodMk continuous_im) (fun z => z.im_pos)

/-- The actual capped physical Maass wave belongs to hyperbolic L² on the
translation strip. Its exponent is fixed by the certificate, not by r or b. -/
theorem principalEulerPhysical_weighted_memLp {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    MemLp (AsymptoticWeightedBranches.stripSection P.ε (P.s+3) 0
      (principalEulerPhysical b r σ)) 2 volume := by
  have hε := P.epsilon_pos
  let F := principalEulerPhysical b r σ
  let f := AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0 F
  have hf : Continuous f := by
    have hw : Continuous (fun z : ℍ => (((min (z.im/P.ε) 1)^(P.s+3):ℝ):ℂ)) := by fun_prop
    convert! hw.mul (principalEulerPhysical_continuous_upper hb.polynomialGrowth r σ) using 1
    funext z
    simp only [f,AsymptoticWeightedBranches.weighted,pow_zero,mul_one,F,Pi.mul_apply]

  obtain ⟨C,hC,hglobal⟩ := principalEulerPhysical_global_height hN A P r σ hb
  obtain ⟨D,_,hhigh⟩ := principalEulerWave_height_bound hb.polynomialGrowth r σ 0 P.ε P.epsilon_pos
  let B := P.ε^2/P.ε^(P.s+3)*C
  apply strip_memLp_of_height_bounds f hf P.ε B D P.epsilon_pos
  · intro z hz
    have hn : ‖f z‖=(z.im/P.ε)^(P.s+3)*‖F z‖ := by
      dsimp [f]
      rw [AsymptoticWeightedBranches.weighted_low P.epsilon_pos _ _ _ z hz]
      simp only [pow_zero,mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
    rw [hn]
    have he : (z.im/P.ε)^(P.s+3)*‖F z‖=
        (z.im^2/P.ε^(P.s+3))*(z.im^P.s*‖F z‖)*z.im := by
      rw [div_pow,pow_add]
      ring
    rw [he]
    change _≤(P.ε^2/P.ε^(P.s+3)*C)*z.im
    gcongr
    exact hglobal z z.im_pos
  · intro z hz
    dsimp [f]
    rw [AsymptoticWeightedBranches.weighted_high P.epsilon_pos _ _ _ z hz]
    simp only [pow_zero,one_mul]
    change ‖principalEulerWave b r σ (z.re,z.im)‖≤D
    simpa only [pow_zero,one_mul] using hhigh z.re z.im hz

/-- Canonical L² equivalence class of the actual weighted reconstruction. -/
def principalEulerWeightedLp {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) : AsymptoticHyperbolicSlash.Space :=
  (principalEulerPhysical_weighted_memLp hN A P r σ hb).toLp _

theorem principalEulerWeightedLp_coeFn {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    principalEulerWeightedLp hN A P r σ hb =ᵐ[volume]
      AsymptoticWeightedBranches.stripSection P.ε (P.s+3) 0 (principalEulerPhysical b r σ) :=
  MemLp.coeFn_toLp _

#print axioms principalEulerPhysical_continuous_upper
#print axioms principalEulerPhysical_weighted_memLp
#print axioms principalEulerWeightedLp
#print axioms principalEulerWeightedLp_coeFn

end QuantitativeMaass
