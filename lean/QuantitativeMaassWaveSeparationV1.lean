module

public import QuantitativeMaassReflectionWaveV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open AsymptoticCongruenceStrip
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The second time derivative at zero recovers the signed energy. -/
theorem signedCosine_second_derivative_zero (x : ℝ) :
    deriv (deriv (fun t => Wave.signedCosine t x)) 0 = -x := by
  let D := fun t => -Real.sin (t*Real.sqrt x)*Real.sqrt x+
    Real.sinh (t*Real.sqrt (-x))*Real.sqrt (-x)
  have hd (t : ℝ) : HasDerivAt (fun t => Wave.signedCosine t x) (D t) t := by
    convert (((hasDerivAt_id t).mul_const (Real.sqrt x)).cos.add
      (((hasDerivAt_id t).mul_const (Real.sqrt (-x))).cosh)).sub_const 1 using 1 <;>
      simp [Wave.signedCosine,D]
  have heq : deriv (fun t => Wave.signedCosine t x)=D := funext (fun t => (hd t).deriv)
  rw [heq]
  have hsin := ((((hasDerivAt_id (0:ℝ)).mul_const (Real.sqrt x)).sin).neg).mul_const (Real.sqrt x)
  have hsinh := (((hasDerivAt_id (0:ℝ)).mul_const (Real.sqrt (-x))).sinh).mul_const (Real.sqrt (-x))
  have hD : HasDerivAt D (-(Real.sqrt x)^2+(Real.sqrt (-x))^2) 0 := by
    convert hsin.add hsinh using 1
    · rfl
    · simp [pow_two]
  rw [hD.deriv]
  rcases le_total 0 x with hx|hx
  · rw [Real.sq_sqrt hx,Real.sqrt_eq_zero_of_nonpos (by linarith)]
    ring
  · rw [Real.sqrt_eq_zero_of_nonpos hx,Real.sq_sqrt (by linarith)]
    ring

/-- All real times of the actual signed wave distinguish any two energies. -/
theorem signedCosine_separates_energy (x y : ℝ)
    (h : ∀ t,Wave.signedCosine t x=Wave.signedCosine t y) : x=y := by
  have hf : (fun t => Wave.signedCosine t x)=(fun t => Wave.signedCosine t y) := funext h
  have hh := congrArg (fun f : ℝ → ℝ => deriv (deriv f) 0) hf
  rw [signedCosine_second_derivative_zero,signedCosine_second_derivative_zero] at hh
  linarith

/-- Any bounded operator commuting with the genuine wave has zero matrix
coefficients between distinct genuine energy eigenvalues. -/
theorem wave_commuting_energy_coefficient_zero (N : ℕ)
    (U : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hU : ∀ t,Commute U (Wave.shiftedQuotientWave N t))
    (u v : AutomorphicSpace N) (e f : ℝ) (he : 0≤e) (hf : 0≤f)
    (hu : FriedrichsGraph N u ((e:ℂ) • u))
    (hv : FriedrichsGraph N v ((f:ℂ) • v)) (hne : e≠f) :
    inner ℂ u (U v)=0 := by
  by_contra hz
  have heq (t : ℝ) : Wave.signedCosine t (e-1/4)=Wave.signedCosine t (f-1/4) := by
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (Wave.shiftedQuotientWave_isSelfAdjoint N t) u (U v)
    have hcomm : U (Wave.shiftedQuotientWave N t v)=Wave.shiftedQuotientWave N t (U v) :=
      DFunLike.congr_fun (hU t) v
    change inner ℂ (Wave.shiftedQuotientWave N t u) (U v)=
      inner ℂ u (Wave.shiftedQuotientWave N t (U v)) at hs
    rw [Wave.shiftedQuotientWave_eigen N he hu,← hcomm,
      Wave.shiftedQuotientWave_eigen N hf hv,map_smul,
      inner_smul_left (𝕜:=ℂ) u (U v),inner_smul_right (𝕜:=ℂ) u (U v),Complex.conj_ofReal] at hs
    apply Complex.ofReal_injective
    exact mul_right_cancel₀ hz hs
  have hh := signedCosine_separates_energy (e-1/4) (f-1/4) heq
  exact hne (by linarith)

#print axioms signedCosine_second_derivative_zero
#print axioms signedCosine_separates_energy
#print axioms wave_commuting_energy_coefficient_zero

end QuantitativeMaass
