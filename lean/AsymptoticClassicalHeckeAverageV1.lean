module

public import AsymptoticClassicalHeckeFourierV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalDiscriminant
open scoped ModularForm

/-- Averaging the p upper-triangular Fourier branches removes precisely
 the exponents not divisible by p. -/
theorem qParam_branch_power_sum (p : ℕ) (hp : 0 < p) (n : ℕ) (z : ℍ) :
    (∑ a : Fin p, Function.Periodic.qParam 1
      (affine (1 / p) (by positivity) ((a.val : ℝ) / p) z) ^ n) =
      if p ∣ n then (p : ℂ) * Function.Periodic.qParam 1 z ^ (n / p) else 0 := by
  classical
  simp_rw [qParam_hecke_branch p hp, mul_pow, ← pow_mul, Nat.mul_comm _ n, pow_mul]
  rw [← Finset.mul_sum, root_filter p hp]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ := hn
    rw [pow_mul, qParam_width_pow p hp, Nat.mul_div_cancel_left m hp]
    ring
  · simp

/-- The analytic averaging operator occurring in both T_p and U_p. -/
def heckeAverage (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ a : Fin p, f (affine (1 / p) (by positivity) ((a.val : ℝ) / p) z)

/-- Fourier coefficient decimation for an actual convergent Fourier series. -/
theorem hasSum_heckeAverage (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ) (c : ℕ → ℂ)
    (hf : ∀ z : ℍ, HasSum (fun n => c n * Function.Periodic.qParam 1 z ^ n) (f z))
    (z : ℍ) :
    HasSum (fun n => c (p * n) * Function.Periodic.qParam 1 z ^ n) (heckeAverage p hp f z) := by
  classical
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  let g : ℕ → ℂ := fun n => if p ∣ n then c n * Function.Periodic.qParam 1 z ^ (n / p) else 0
  have hs : HasSum g (heckeAverage p hp f z) := by
    have hs := (hasSum_sum (s := Finset.univ) (fun a (_ : a ∈ (Finset.univ : Finset (Fin p))) =>
      hf (affine (1 / p) (by positivity) ((a.val : ℝ) / p) z))).mul_left (p : ℂ)⁻¹
    apply hs.congr_fun
    intro n
    rw [← Finset.mul_sum, qParam_branch_power_sum p hp n z]
    dsimp only [g]
    split_ifs <;> simp [hpC, mul_left_comm]
  have hi : Function.Injective (fun n : ℕ => p * n) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h
  have hn (n : ℕ) (h : n ∉ Set.range (fun m : ℕ => p * m)) : g n = 0 := by
    have hnd : ¬ p ∣ n := by rintro ⟨m, rfl⟩; exact h ⟨m, rfl⟩
    simp [g, hnd]
  have ht := (hi.hasSum_iff hn).mpr hs
  simpa [Function.comp_def, g, Nat.mul_div_cancel_left _ hp] using ht

#print axioms qParam_branch_power_sum
#print axioms hasSum_heckeAverage

end AsymptoticClassicalCusp
