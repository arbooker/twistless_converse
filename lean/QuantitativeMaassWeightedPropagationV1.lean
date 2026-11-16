module

public import QuantitativeMaassWeightedSupportV1
public import QuantitativeMaassExponentialLimitV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassWeighted QuantitativeArithmeticMaassWave
open QuantitativeArithmeticMaassGradient

def initialEnergy (N : ℕ) (u : QuotientEnergySpace N) : ℝ :=
  ‖quotientGradient N true u‖^2+‖quotientGradient N false u‖^2+‖ambientInclusion N u‖^2

theorem initial_exponential_energy (N : ℕ) (b : Cutoff N) {a : ℝ} (ha : 0≤a)
    (u : QuotientEnergySpace N) (c : ℝ)
    (hu : ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re → ambientInclusion N u Z=0)
    (hg : ∀ i : Bool, ∀ᵐ Z ∂quotientMeasure N,
      c<(upperFunction b.value Z).re → quotientGradient N i u Z=0) :
    energy N (exponentialCutoff N b a ha) u 0≤Real.exp (2*a*c)*initialEnergy N u := by
  have hi := exponential_initial_bound N b ha (ambientInclusion N u) c hu
  have hx := exponential_initial_bound N b ha (quotientGradient N true u) c (hg true)
  have hy := exponential_initial_bound N b ha (quotientGradient N false u) c (hg false)
  unfold energy initialEnergy
  simp only [ZeroMemClass.coe_zero,map_zero,norm_zero,zero_pow (by omega : 2≠0),zero_add]
  nlinarith only [hi,hx,hy]

theorem wave_mass_le_energy (N : ℕ) (b : Cutoff N) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (t : ℝ) :
    ‖multiplier N b (Wave.shiftedQuotientWave N t x).val‖^2≤waveEnergy N b x y t := by
  have hi : ambientInclusion N (quotientEnergyWave N x y t)=
      (Wave.shiftedQuotientWave N t x).val :=
    congrArg Subtype.val (quotientEnergyWave_value N hxy t)
  unfold waveEnergy energy
  rw [hi]
  nlinarith [sq_nonneg ‖multiplier N b (quotientWaveVelocity N x y t).val‖,
    sq_nonneg ‖multiplier N b (quotientGradient N true (quotientEnergyWave N x y t))‖,
    sq_nonneg ‖multiplier N b (quotientGradient N false (quotientEnergyWave N x y t))‖]

/-- Off-diagonal weighted estimate for the actual quotient wave, from literal
almost-everywhere support conditions on its initial value and gradients. -/
theorem separated_wave_estimate (N : ℕ) (b w : Cutoff N) {a : ℝ} (ha : 0≤a)
    {x y z : AutomorphicSpace N} (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z)
    (c d : ℝ)
    (hu : ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      ambientInclusion N (graphEnergyLift N x y) Z=0)
    (hg : ∀ i : Bool, ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      quotientGradient N i (graphEnergyLift N x y) Z=0)
    (hw : ∀ᵐ Z ∂quotientMeasure N,
      (upperFunction b.value Z).re<d → upperFunction w.value Z=0)
    {t : ℝ} (ht : 0≤t) :
    ‖multiplier N w (Wave.shiftedQuotientWave N t x).val‖^2≤
      (w.bound^2*initialEnergy N (graphEnergyLift N x y)*Real.exp ((5/4)*t))*
        Real.exp (-(2*(d-c-|b.gradientBound| * t))*a) := by
  have ho := exponential_observation_bound N b w ha (Wave.shiftedQuotientWave N t x).val d hw
  have hm := wave_mass_le_energy N (exponentialCutoff N b a ha) hxy t
  have he := exponential_wave_bound N b ha hxy hyz ht
  have hi := initial_exponential_energy N b ha (graphEnergyLift N x y) c hu hg
  have he0 : waveEnergy N (exponentialCutoff N b a ha) x y 0=
      energy N (exponentialCutoff N b a ha) (graphEnergyLift N x y) 0 := by
    simp only [waveEnergy,quotientEnergyWave,Wave.shiftedQuotientWave_zero,
      ContinuousLinearMap.id_apply,quotientWaveVelocity_zero]
  rw [he0] at he
  have h1 := he.trans (mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le)
  have h2 := ho.trans (mul_le_mul_of_nonneg_left (hm.trans h1)
    (mul_nonneg (sq_nonneg w.bound) (Real.exp_pos _).le))
  have hex : -(2*a*d)+(2*a*c)+((2*(a*|b.gradientBound|)+5/4)*t)=
      (5/4)*t+(-(2*(d-c-|b.gradientBound| * t))*a) := by ring
  have heq : w.bound^2*Real.exp (-(2*a*d))*
      (Real.exp (2*a*c)*initialEnergy N (graphEnergyLift N x y)*
        Real.exp ((2*(a*|b.gradientBound|)+5/4)*t))=
      (w.bound^2*initialEnergy N (graphEnergyLift N x y)*Real.exp ((5/4)*t))*
        Real.exp (-(2*(d-c-|b.gradientBound| * t))*a) := by
    calc
      _ = w.bound^2*initialEnergy N (graphEnergyLift N x y)*
          (Real.exp (-(2*a*d))*Real.exp (2*a*c)*
            Real.exp ((2*(a*|b.gradientBound|)+5/4)*t)) := by ring
      _ = _ := by rw [← Real.exp_add,← Real.exp_add,hex,Real.exp_add]; ring
  exact heq ▸ h2

/-- Propagation across separated smooth invariant weights. If the initial
value and its energy gradients lie below c, then an observation above d is
zero until d-c exceeds the gradient bound times elapsed time. -/
theorem separated_wave_vanishes (N : ℕ) (b w : Cutoff N)
    {x y z : AutomorphicSpace N} (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z)
    (c d : ℝ)
    (hu : ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      ambientInclusion N (graphEnergyLift N x y) Z=0)
    (hg : ∀ i : Bool, ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      quotientGradient N i (graphEnergyLift N x y) Z=0)
    (hw : ∀ᵐ Z ∂quotientMeasure N,
      (upperFunction b.value Z).re<d → upperFunction w.value Z=0)
    {t : ℝ} (ht : 0≤t) (hsep : c+|b.gradientBound| * t<d) :
    multiplier N w (Wave.shiftedQuotientWave N t x).val=0 := by
  have h := eq_zero_of_exponential_bounds
    (sq_nonneg ‖multiplier N w (Wave.shiftedQuotientWave N t x).val‖)
    (show 0<2*(d-c-|b.gradientBound| * t) by linarith)
    (fun a ha => separated_wave_estimate N b w ha hxy hyz c d hu hg hw ht)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

#print axioms separated_wave_estimate
#print axioms separated_wave_vanishes

end QuantitativeMaass.Weighted
