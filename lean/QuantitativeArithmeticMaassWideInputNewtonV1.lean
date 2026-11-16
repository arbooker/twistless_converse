module

public import QuantitativeArithmeticMaassWideInputRatesV1
public import QuantitativeMaassStrongNewtonSourceCostV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter QuantitativeNinaMaass QuantitativeHolomorphic ContinuousLinearMap
open scoped Topology
namespace QuantitativeMaass.WideInput

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

variable (N : ℕ) [NeZero N] (hN : 0<N) (S : CuspEnergySpectrum N hN)
  {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)

/-- Weighted polynomial compression uniform over growing input windows.
The coefficient cost, degree and input width are separate explicit parameters. -/
theorem weighted_polynomial_compression
    (a c Dinput W : ℝ) (ha : 0≤a) (hDi : 0≤Dinput)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧ ∃ F : ℝ → ℝ,
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*F t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,∀ B : ℝ,1≤B → B≤Real.exp (Dinput*Strong.strongScale t) →
        ∀ p : Polynomial ℝ,(p.natDegree:ℝ)≤a*Strong.strongScale t →
        (p.support.card:ℝ)*(∑ j∈p.support,(p.coeff j)^2)≤Real.exp (c*Strong.strongScale t) →
        ∀ Bouter : ℝ,radius B (Real.exp (D*Strong.strongScale t)) p.natDegree≤Bouter →
        ∀ {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℂ (S.band (t-B) (t+B))),
        finiteSourceEnergy v
          ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) p).comp (S.band (t-B) (t+B)).subtypeL-
          (Polynomial.aeval ((projection S t Bouter).comp (newSignWeightedGram N hN hδ hν χ)) p).comp
            (S.band (t-B) (t+B)).subtypeL)≤F t := by
  obtain ⟨D,hDiD,hD,M,hM,hbound⟩ := weighted_fixed_compression N hN S hδ hν χ a Dinput (W+c)
    ha hDi ε hε hproduct
  let F := fun t => Real.exp (c*Strong.strongScale t)*|M t|
  refine ⟨D,hDiD,hD,F,?_,?_⟩
  · have hh := hM.abs
    simp only [abs_zero] at hh
    apply hh.congr'
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    dsimp only [F]
    rw [abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (mul_pos ht he),add_mul,Real.exp_add]
    ring
  · filter_upwards [hbound] with t ht
    intro B hB hBi p hp hc Bouter hout ι _ v
    have hid :
        (Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) p).comp (S.band (t-B) (t+B)).subtypeL-
        (Polynomial.aeval ((projection S t Bouter).comp (newSignWeightedGram N hN hδ hν χ)) p).comp
          (S.band (t-B) (t+B)).subtypeL=
        (∑ j∈p.support,p.coeff j • ambientPath S hδ hν χ t B j)-
          (∑ j∈p.support,p.coeff j • fixedPath S hδ hν χ t B Bouter j) := by
      simp only [polynomial_aeval_sum,finsetSum_comp,smul_comp,ambientPath_power,fixedPath_power]
    rw [hid]
    have hjbound (j : ℕ) (hj : j∈p.support) :
        finiteSourceEnergy v (ambientPath S hδ hν χ t B j-fixedPath S hδ hν χ t B Bouter j)≤|M t| := by
      have hjp := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
      have hjr : (j:ℝ)≤a*Strong.strongScale t := (by exact_mod_cast hjp : (j:ℝ)≤p.natDegree).trans hp
      have hr := (radius_mono B (Real.exp (D*Strong.strongScale t)) (Real.exp_pos _).le hjp).trans hout
      exact (ht B hB hBi j hjr Bouter hr v).trans (le_abs_self _)
    exact (finiteSourceEnergy_combination_difference v p.support p.coeff _ _ |M t| hjbound).trans
      (mul_le_mul_of_nonneg_right hc (abs_nonneg _))

/-- The actual scheduled Newton polynomial can be compressed to a fixed outer
band after the cylinder packet has been compressed to an exponentially wide
input band. Its degree and coefficient bounds are proved independently. -/
theorem weighted_newton_compression
    (Dinput W : ℝ) (hDi : 0≤Dinput)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧ ∃ F : ℝ → ℝ,
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*F t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,∀ B : ℝ,1≤B → B≤Real.exp (Dinput*Strong.strongScale t) →
        ∀ Bouter : ℝ,radius B (Real.exp (D*Strong.strongScale t))
          (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree≤Bouter →
        ∀ {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℂ (S.band (t-B) (t+B))),
        finiteSourceEnergy v
          ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ)
            (inverseSqrtPolynomial (Strong.bandNewtonDepth t))).comp (S.band (t-B) (t+B)).subtypeL-
          (Polynomial.aeval ((projection S t Bouter).comp (newSignWeightedGram N hN hδ hν χ))
            (inverseSqrtPolynomial (Strong.bandNewtonDepth t))).comp
              (S.band (t-B) (t+B)).subtypeL)≤F t := by
  obtain ⟨D,hDiD,hD,F,hF,hbound⟩ := weighted_polynomial_compression N hN S hδ hν χ
    2 (2*Real.log 48) Dinput W (by norm_num) hDi ε hε hproduct
  refine ⟨D,hDiD,hD,F,hF,?_⟩
  filter_upwards [hbound,Strong.bandNewtonDepth_source_cost] with t ht hc
  intro B hB hBi
  exact ht B hB hBi (inverseSqrtPolynomial (Strong.bandNewtonDepth t)) hc.1 hc.2

#print axioms weighted_polynomial_compression
#print axioms weighted_newton_compression
end QuantitativeMaass.WideInput
