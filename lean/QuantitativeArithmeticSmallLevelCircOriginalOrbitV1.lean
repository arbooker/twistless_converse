module

public import QuantitativeArithmeticSmallLevelCircOrbitV1
public import QuantitativeArithmeticRamifiedFullTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane Matrix FinitenessOriginalInput FinitenessOriginalFourier
open FinitenessFourierConstruction SmallLevelOriginal AsymptoticOrbitDecode
open AsymptoticClassicalPetersson QuantitativeEulerOldProjectionHolomorphic
open AsymptoticFreshMatrices AsymptoticRegularObservationRows
open AsymptoticRationalBranches AsymptoticSlashGauge
open scoped ModularForm

 theorem orbit_ramified (p m : ℕ) (hp : 0 < p) (F : ℂ → ℂ) (z : ℍ) (a : Fin p) :
    orbit m (fun w : ℍ => F w) z (ramifiedLabel p hp a) =
      (z.im : ℂ)^m / (p : ℂ)^m * F (((z : ℂ)+(a.val : ℂ))/p) := by
  rw [ramifiedLabel, orbit_ofMatrix]
  simp only [ramified, realMatrix_ramified, Rat.cast_natCast, weighted_even]
  simpa only [Complex.ofReal_natCast, mul_assoc] using
    AsymptoticRamifiedBranch.normalized_branch
      (show (0 : ℝ)<p by exact_mod_cast hp) a.val m F z

 theorem original_ramified_orbit {N m : ℕ} (hm : 0 < m) {f : ℕ → ℂ}
    (hf : IsSolution N (2*m) f) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (z : ℍ) (g : AsymptoticRationalGroup.Group) :
    (∑ a : Fin p, orbit m (fourierFunction (2*m) f) z (ramifiedLabel p hp.pos a*g)) =
      (f p * (Real.sqrt p : ℂ)) * orbit m (fourierFunction (2*m) f) z g := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨τ, _, hg⟩ := hf.growth
  have hs := AsymptoticRamifiedFourier.average_of_row
    (fullCoefficients f (2*(h+1))) (polynomial_bound hf.zero hg _)
    hp.pos ((f p * (Real.sqrt p : ℂ)) * (p : ℂ)^h)
    (AsymptoticRamifiedCoefficients.simple_relation hf.toEulerData hp hpN h)
    (g • z).im_pos
  simp only [orbit_mul, ← Finset.mul_sum]
  have hh : (∑ a : Fin p, orbit (h+1) (fourierFunction (2*(h+1)) f)
      (g • z) (ramifiedLabel p hp.pos a)) =
      (f p * (Real.sqrt p : ℂ)) * weighted ((2*(h+1) : ℕ) : ℤ)
        (fourierFunction (2*(h+1)) f) (g • z) := by
    change (∑ a : Fin p, orbit (h+1)
      (fun w : ℍ => fourier (fullCoefficients f (2*(h+1))) w)
      (g • z) (ramifiedLabel p hp.pos a)) = _
    simp only [orbit_ramified, ← Finset.mul_sum]
    let T : ℕ → ℂ := fun a => fourier (fullCoefficients f (2*(h+1)))
      ((((g • z : ℍ) : ℂ)+(a : ℂ))/(p : ℂ))
    have hsum : (∑ a : Fin p, T a.val) = ∑ a ∈ Finset.range p, T a :=
      Fin.sum_univ_eq_sum_range T p
    change _ * (∑ a : Fin p, T a.val) = _
    rw [hsum]
    change _ * (∑ a ∈ Finset.range p, fourier (fullCoefficients f (2*(h+1)))
      ((((g • z : ℍ) : ℂ)+(a : ℂ))/(p : ℂ))) = _
    rw [hs, weighted_even]
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [pow_succ]
    change _ = (f p * (Real.sqrt p : ℂ)) *
      ((↑(g • z).im : ℂ)^(h+1) * fourier (fullCoefficients f (2*(h+1))) ((g • z : ℍ) : ℂ))
    field_simp
    simp only [pow_succ]
    ring
  rw [hh, orbit]
  ring

 theorem orbit_fricke (N m : ℕ) (hN : 0 < N) (F : ℂ → ℂ) (z : ℍ) :
    orbit m (fun w : ℍ => F w) z (frickeLabel N hN) =
      (z.im : ℂ)^m / (((Real.sqrt N : ℂ) * (z : ℂ))^(2*m)) *
        F (-1/((N : ℂ)*(z : ℂ))) := by
  rw [frickeLabel, orbit_ofMatrix, realMatrix_branch]
  simp only [Rat.cast_natCast, Rat.cast_zero]
  rw [weighted_even, ← mul_assoc, AsymptoticHyperbolicSlash.normalized_slash
    (AsymptoticReconstructionBranch.branch (N : ℝ) 0 0 (by exact_mod_cast hN.ne'))
    (by rw [AsymptoticReconstructionBranch.branch_det]; exact_mod_cast hN) m
    (fun w : ℍ => F w) z,
    AsymptoticReconstructionBranch.branch_det,
    AsymptoticReconstructionBranch.branch_action (show (0 : ℝ)<N by exact_mod_cast hN)]
  have hd : denom (AsymptoticReconstructionBranch.branch (N : ℝ) 0 0 (by exact_mod_cast hN.ne')) z =
      (N : ℂ)*(z : ℂ) := by
    simp [denom, AsymptoticReconstructionBranch.branch, GeneralLinearGroup.mkOfDetNeZero]
  rw [hd]
  simp only [Complex.ofReal_natCast, Complex.ofReal_zero, add_zero]
  have hsq : (Real.sqrt N : ℂ)^2 = (N : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    rfl
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hz : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  have hepow : ((Real.sqrt N : ℂ)*(z : ℂ))^(2*m) =
      (N : ℂ)^m*(z : ℂ)^(2*m) := by rw [mul_pow, pow_mul, hsq]
  rw [hepow, mul_pow]
  have hpow : (N : ℂ)^(2*m) = ((N : ℂ)^m)^2 := by rw [mul_comm 2 m, pow_mul]
  rw [hpow]
  field_simp

 theorem original_fricke_orbit {N m : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf : IsSolution N (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ z g,
      χ * orbit m (fourierFunction (2*m) f) z (frickeLabel N hN*g) =
        orbit m (fourierFunction (2*m) f) z g := by
  obtain ⟨ε,hε,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  let χ : ℂ := ε*Complex.I^(2*m)
  have hχ : χ=1 ∨ χ= -1 := by
    have hi : Complex.I^(2*m)=(-1 : ℂ)^m := by rw [pow_mul, Complex.I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [χ,hi,h]
  refine ⟨χ,hχ,?_⟩
  intro z g
  have h := hlaw 1 (by decide) ((g • z : ℍ) : ℂ) (g • z).im_pos
  simp only [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist] at h
  have he : fourierFunction (2*m) f (g • z) =
      χ/(((Real.sqrt N : ℂ)*(g • z : ℍ))^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((N : ℂ)*(g • z : ℍ))) := by
    simpa [χ, fourierFunction] using h
  rw [orbit_mul]
  change χ * (phase g m z * orbit m
    (fun w : ℍ => fourier (fullCoefficients f (2*m)) w) (g • z) (frickeLabel N hN)) = _
  rw [orbit_fricke, orbit, weighted_even, he]
  ring

#print axioms original_ramified_orbit
#print axioms original_fricke_orbit
end QuantitativeArithmeticSmallLevelCirc
