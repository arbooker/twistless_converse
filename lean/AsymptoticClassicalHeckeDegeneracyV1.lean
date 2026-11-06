module

public import AsymptoticClassicalDiscriminantLevelV1
public import Mathlib.RingTheory.PowerSeries.Expand

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

/-- Dilation raises the analytic Fourier parameter to the corresponding power. -/
theorem qParam_dilation (p : ℕ) (hp : 0 < p) (z : ℍ) :
    Function.Periodic.qParam 1 (dilationReal p hp • z : ℍ) =
      Function.Periodic.qParam 1 z ^ p := by
  rw [AsymptoticClassicalDiscriminant.dilation_action]
  simp only [AsymptoticClassicalDiscriminant.affine, Function.Periodic.qParam,
    Complex.ofReal_one, div_one, Complex.ofReal_natCast, Complex.ofReal_zero, add_zero]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The Fourier series of an actual degeneracy form is obtained by replacing
 the formal parameter by its p-th power. -/
theorem qExpansion_degeneracy (N p : ℕ) [NeZero N] (hp : 0 < p) (k : ℤ)
    (f : CuspForm (level N) k) :
    qExpansion 1 (degeneracy N p hp k f) =
      PowerSeries.expand p hp.ne' (qExpansion 1 f) := by
  classical
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  ext n
  symm
  apply ModularFormClass.qExpansion_coeff_unique (f := degeneracy N p hp k f)
    (c := fun m => (PowerSeries.expand p hp.ne' (qExpansion 1 f)).coeff m)
    zero_lt_one (level_one_period (p * N)) (m := n)
  intro z
  have hi : Function.Injective (fun n : ℕ => p * n) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h
  apply (hi.hasSum_iff (fun n hn => ?_)).mp
  · change HasSum (fun n : ℕ =>
      (PowerSeries.expand p hp.ne' (qExpansion 1 f)).coeff (p * n) •
        Function.Periodic.qParam 1 z ^ (p * n)) _
    simp only [PowerSeries.coeff_expand_mul, pow_mul, ← qParam_dilation p hp z,
      degeneracy_apply]
    simpa only [smul_eq_mul] using ModularForm.hasSum_qExpansion
      (f := f) zero_lt_one (level_one_period N) (dilationReal p hp • z)
  · have hnd : ¬ p ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [PowerSeries.coeff_expand_of_not_dvd p hp.ne' _ hnd]

/-- Exact coefficient transport along the classical degeneracy map. -/
theorem coeff_degeneracy (N p : ℕ) [NeZero N] (hp : 0 < p) (k : ℤ)
    (f : CuspForm (level N) k) (n : ℕ) :
    (qExpansion 1 (degeneracy N p hp k f)).coeff n =
      if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0 := by
  rw [qExpansion_degeneracy, PowerSeries.coeff_expand]

#print axioms qParam_dilation
#print axioms qExpansion_degeneracy
#print axioms coeff_degeneracy

end AsymptoticClassicalCusp
