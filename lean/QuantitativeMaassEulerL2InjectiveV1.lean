module

public import QuantitativeMaassEulerWeightedL2V1
public import QuantitativeMaassEulerInjectiveV1
public import QuantitativeMaassEulerWaveAnalyticV1
public import Mathlib.MeasureTheory.Measure.OpenPos
public import AsymptoticClassicalHolomorphicDensityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

/-- Equality of actual capped strip classes loses no pointwise information
in the open strip, because the weight is strictly positive. -/
theorem weighted_strip_ae_eq_open (ε : ℝ) (hε : 0<ε) (t : ℕ)
    (f g : ℂ → ℂ) (hf : Continuous (fun z : ℍ => f z))
    (hg : Continuous (fun z : ℍ => g z))
    (he : AsymptoticWeightedBranches.stripSection ε t 0 f =ᵐ[volume]
      AsymptoticWeightedBranches.stripSection ε t 0 g) :
    ∀ z : ℍ,0<z.re → z.re<1 → f z=g z := by
  let U : Set ℍ := {z | 0<z.re ∧ z.re<1}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hwf : Continuous (AsymptoticWeightedBranches.weighted ε t 0 f) := by
    unfold AsymptoticWeightedBranches.weighted
    exact ((by fun_prop : Continuous (fun z : ℍ => (((min (z.im/ε) 1)^t:ℝ):ℂ))).mul
      (by fun_prop : Continuous (fun z : ℍ => (z.im:ℂ)^0))).mul hf
  have hwg : Continuous (AsymptoticWeightedBranches.weighted ε t 0 g) := by
    unfold AsymptoticWeightedBranches.weighted
    exact ((by fun_prop : Continuous (fun z : ℍ => (((min (z.im/ε) 1)^t:ℝ):ℂ))).mul
      (by fun_prop : Continuous (fun z : ℍ => (z.im:ℂ)^0))).mul hg
  have hae : AsymptoticWeightedBranches.weighted ε t 0 f =ᵐ[volume.restrict U]
      AsymptoticWeightedBranches.weighted ε t 0 g := by
    filter_upwards [ae_restrict_of_ae he,ae_restrict_mem hU.measurableSet] with z hz hzu
    have hs : z∈AsymptoticMassTransport.strip := ⟨hzu.1.le,hzu.2⟩
    simpa only [AsymptoticWeightedBranches.stripSection,Set.indicator_of_mem hs] using hz
  have hpoint := Measure.eqOn_open_of_ae_eq hae hU hwf.continuousOn hwg.continuousOn
  intro z hz0 hz1
  have hh := hpoint ⟨hz0,hz1⟩
  simp only [AsymptoticWeightedBranches.weighted,pow_zero,mul_one] at hh
  apply mul_left_cancel₀ _ hh
  exact_mod_cast (pow_pos (lt_min (div_pos z.im_pos hε) zero_lt_one) t).ne'

/-- Passing to weighted L² equivalence classes preserves the original
Euler coefficient sequence. Analytic continuation along each horizontal
line upgrades open-strip equality to the whole physical half-plane. -/
theorem principalEulerWeightedLp_injective {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b c : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (hc : MaassOriginal.IsEulerSolution N (.principal r) σ c)
    (he : principalEulerWeightedLp hN A P r σ hb=principalEulerWeightedLp hN A P r σ hc) : b=c := by
  have hae : AsymptoticWeightedBranches.stripSection P.ε (P.s+3) 0 (principalEulerPhysical b r σ) =ᵐ[volume]
      AsymptoticWeightedBranches.stripSection P.ε (P.s+3) 0 (principalEulerPhysical c r σ) := by
    exact (principalEulerWeightedLp_coeFn hN A P r σ hb).symm.trans
      (he ▸ principalEulerWeightedLp_coeFn hN A P r σ hc)
  have hstrip := weighted_strip_ae_eq_open P.ε P.epsilon_pos (P.s+3) _ _
    (principalEulerPhysical_continuous_upper hb.polynomialGrowth r σ)
    (principalEulerPhysical_continuous_upper hc.polynomialGrowth r σ) hae
  apply principalEulerWave_injective hb.polynomialGrowth hc.polynomialGrowth (hb.zero.trans hc.zero.symm) r σ
  intro x y hy
  have hlocal : (fun x : ℝ => principalEulerWave b r σ (x,y)) =ᶠ[𝓝 (1/2:ℝ)]
      (fun x : ℝ => principalEulerWave c r σ (x,y)) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)] with u hu
    exact hstrip ⟨⟨u,y⟩,hy⟩ hu.1 hu.2
  have heq := (principalEulerWave_analytic_horizontal hb.polynomialGrowth r σ y hy).eq_of_eventuallyEq
    (principalEulerWave_analytic_horizontal hc.polynomialGrowth r σ y hy) hlocal
  exact congrFun heq x

#print axioms weighted_strip_ae_eq_open
#print axioms principalEulerWeightedLp_injective

end QuantitativeMaass
