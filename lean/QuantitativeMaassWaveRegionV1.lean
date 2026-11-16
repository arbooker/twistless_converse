module

public import QuantitativeMaassWeightedPropagationV1
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

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

def regionField (N : ℕ) (s : Set ℍ) (hs : MeasurableSet s)
    (f : Lp ℂ 2 (quotientMeasure N)) : Lp ℂ 2 (quotientMeasure N) :=
  (MemLp.indicator hs (Lp.memLp f)).toLp (s.indicator f)

theorem regionField_ae (N : ℕ) (s : Set ℍ) (hs : MeasurableSet s)
    (f : Lp ℂ 2 (quotientMeasure N)) :
    ∀ᵐ Z ∂quotientMeasure N, regionField N s hs f Z=s.indicator f Z :=
  MemLp.coeFn_toLp _

theorem region_exponential_bound (N : ℕ) (b : Cutoff N) {a : ℝ} (ha : 0≤a)
    (f : Lp ℂ 2 (quotientMeasure N)) (s : Set ℍ) (hs : MeasurableSet s) (d : ℝ)
    (hsep : ∀ Z∈s, d≤(upperFunction b.value Z).re) :
    ‖regionField N s hs f‖^2≤Real.exp (-(2*a*d))*
      ‖multiplier N (exponentialCutoff N b a ha) f‖^2 := by
  apply norm_sq_le_of_ae
  filter_upwards [regionField_ae N s hs f,
    multiplier_ae N (exponentialCutoff N b a ha) f] with Z hz hw
  rw [hz,hw,norm_mul,mul_pow]
  change ‖s.indicator (fun Z => f Z) Z‖^2≤
    Real.exp (-(2*a*d))*(‖upperFunction (exponentialValue a b.value) Z‖^2*‖f Z‖^2)
  rw [exponential_norm]
  by_cases hZ : Z∈s
  · rw [Set.indicator_of_mem hZ]
    have he : 1≤Real.exp (-(2*a*d))*Real.exp (a*(upperFunction b.value Z).re)^2 := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      norm_num only [Nat.cast_ofNat]
      nlinarith [mul_le_mul_of_nonneg_left (hsep Z hZ) ha]
    nlinarith only [mul_le_mul_of_nonneg_right he (sq_nonneg ‖f Z‖)]
  · rw [Set.indicator_of_notMem hZ]
    simp only [norm_zero,zero_pow (by omega : 2≠0)]
    positivity

/-- A measurable region beyond the weighted propagation front receives zero
wave. All support hypotheses concern initial data, not the evolved solution. -/
theorem wave_region_zero (N : ℕ) (b : Cutoff N)
    {x y z : AutomorphicSpace N} (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z)
    (c d : ℝ)
    (hu : ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      ambientInclusion N (graphEnergyLift N x y) Z=0)
    (hg : ∀ i : Bool, ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      quotientGradient N i (graphEnergyLift N x y) Z=0)
    (s : Set ℍ) (hs : MeasurableSet s)
    (hsb : ∀ Z∈s, d≤(upperFunction b.value Z).re)
    {t : ℝ} (ht : 0≤t) (hsep : c+|b.gradientBound| * t<d) :
    regionField N s hs (Wave.shiftedQuotientWave N t x).val=0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  apply eq_zero_of_exponential_bounds
    (sq_nonneg ‖regionField N s hs (Wave.shiftedQuotientWave N t x).val‖)
    (show 0<2*(d-c-|b.gradientBound| * t) by linarith)
    (C := initialEnergy N (graphEnergyLift N x y)*Real.exp ((5/4)*t))
  intro a ha
  have ho := region_exponential_bound N b ha (Wave.shiftedQuotientWave N t x).val s hs d hsb
  have hm := wave_mass_le_energy N (exponentialCutoff N b a ha) hxy t
  have he := exponential_wave_bound N b ha hxy hyz ht
  have hi := initial_exponential_energy N b ha (graphEnergyLift N x y) c hu hg
  have he0 : waveEnergy N (exponentialCutoff N b a ha) x y 0=
      energy N (exponentialCutoff N b a ha) (graphEnergyLift N x y) 0 := by
    simp only [waveEnergy,quotientEnergyWave,Wave.shiftedQuotientWave_zero,
      ContinuousLinearMap.id_apply,quotientWaveVelocity_zero]
  rw [he0] at he
  have h1 := he.trans (mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le)
  have h2 := ho.trans (mul_le_mul_of_nonneg_left (hm.trans h1) (Real.exp_pos _).le)
  have hex : -(2*a*d)+(2*a*c)+((2*(a*|b.gradientBound|)+5/4)*t)=
      (5/4)*t+(-(2*(d-c-|b.gradientBound| * t))*a) := by ring
  have heq : Real.exp (-(2*a*d))*
      (Real.exp (2*a*c)*initialEnergy N (graphEnergyLift N x y)*
        Real.exp ((2*(a*|b.gradientBound|)+5/4)*t))=
      (initialEnergy N (graphEnergyLift N x y)*Real.exp ((5/4)*t))*
        Real.exp (-(2*(d-c-|b.gradientBound| * t))*a) := by
    calc
      _ = initialEnergy N (graphEnergyLift N x y)*
          (Real.exp (-(2*a*d))*Real.exp (2*a*c)*
            Real.exp ((2*(a*|b.gradientBound|)+5/4)*t)) := by ring
      _ = _ := by rw [← Real.exp_add,← Real.exp_add,hex,Real.exp_add]; ring
  exact heq ▸ h2

theorem wave_region_ae_zero (N : ℕ) (b : Cutoff N)
    {x y z : AutomorphicSpace N} (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z)
    (c d : ℝ)
    (hu : ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      ambientInclusion N (graphEnergyLift N x y) Z=0)
    (hg : ∀ i : Bool, ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      quotientGradient N i (graphEnergyLift N x y) Z=0)
    (s : Set ℍ) (hs : MeasurableSet s)
    (hsb : ∀ Z∈s, d≤(upperFunction b.value Z).re)
    {t : ℝ} (ht : 0≤t) (hsep : c+|b.gradientBound| * t<d) :
    ∀ᵐ Z ∂quotientMeasure N, Z∈s → (Wave.shiftedQuotientWave N t x).val Z=0 := by
  have hz := wave_region_zero N b hxy hyz c d hu hg s hs hsb ht hsep
  have he := regionField_ae N s hs (Wave.shiftedQuotientWave N t x).val
  rw [hz] at he
  filter_upwards [he,Lp.coeFn_zero ℂ 2 (quotientMeasure N)] with Z hZ h0
  intro hmem
  rw [Set.indicator_of_mem hmem] at hZ
  exact hZ.symm.trans h0

#print axioms wave_region_zero
#print axioms wave_region_ae_zero

end QuantitativeMaass.Weighted
