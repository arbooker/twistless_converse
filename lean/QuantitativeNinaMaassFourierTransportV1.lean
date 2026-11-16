module

public import QuantitativeNinaMaassFourierSeparationV1
public import QuantitativeNinaMaassSmallPeriodsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set MeasureTheory AddCircle
open scoped Topology

/-!
Literal Fourier integrals under the dilation and averaging branches that
occur in the normalized Hecke correspondence. These are general identities
for continuous periodic functions, proved by changes of variables. They do
not assume a Fourier expansion or Hecke coefficient recurrence.
-/

namespace QuantitativeNinaMaass

theorem fourier_argument_add {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

theorem unit_fourier_periodic (n : ℤ) :
    Function.Periodic (fun x : ℝ => fourier n (x : AddCircle (1 : ℝ))) 1 := by
  intro x
  change fourier n ((x + 1 : ℝ) : AddCircle (1 : ℝ)) = fourier n (x : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]

theorem unit_fourier_continuous (n : ℤ) :
    Continuous (fun x : ℝ => fourier n (x : AddCircle (1 : ℝ))) :=
  (fourier n).continuous.comp (AddCircle.continuous_mk' 1)

theorem unit_fourier_integer_dilate (n p : ℤ) (x : ℝ) :
    fourier n (((p : ℝ) * x : ℝ) : AddCircle (1 : ℝ)) =
      fourier (p * n) (x : AddCircle (1 : ℝ)) := by
  simp only [fourier_coe_apply, Int.cast_mul, Complex.ofReal_mul]
  congr 1
  push_cast
  ring

theorem unitLineFourierCoeff_const_mul (f : ℝ → ℂ) (c : ℂ) (n : ℤ) :
    unitLineFourierCoeff (fun x => c * f x) n = c * unitLineFourierCoeff f n := by
  simp only [unitLineFourierCoeff]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  ring

theorem unitLineFourierCoeff_add (f g : ℝ → ℂ) (hf : Continuous f)
    (hg : Continuous g) (n : ℤ) :
    unitLineFourierCoeff (fun x => f x + g x) n =
      unitLineFourierCoeff f n + unitLineFourierCoeff g n := by
  simp only [unitLineFourierCoeff, mul_add]
  exact intervalIntegral.integral_add
    (((unit_fourier_continuous (-n)).mul hf).intervalIntegrable 0 1)
    (((unit_fourier_continuous (-n)).mul hg).intervalIntegrable 0 1)

theorem unitLineFourierCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) (n : ℤ) :
    unitLineFourierCoeff (fun x => ∑ i ∈ s, f i x) n =
      ∑ i ∈ s, unitLineFourierCoeff (f i) n := by
  simp only [unitLineFourierCoeff, Finset.mul_sum]
  exact intervalIntegral.integral_finsetSum (fun i hi =>
    ((unit_fourier_continuous (-n)).mul (hf i hi)).intervalIntegrable 0 1)

/-- The character-weighted mean is unchanged by a real translation. -/
theorem unitLineFourierCoeff_translate_identity (f : ℝ → ℂ)
    (hp : Function.Periodic f 1) (a : ℝ) (n : ℤ) :
    fourier (-n) (a : AddCircle (1 : ℝ)) *
      unitLineFourierCoeff (fun x => f (x + a)) n = unitLineFourierCoeff f n := by
  have hper : Function.Periodic
      (fun x : ℝ => fourier (-n) (x : AddCircle (1 : ℝ)) * f x) 1 := by
    intro x
    change fourier (-n) ((x + 1 : ℝ) : AddCircle (1 : ℝ)) * f (x + 1) = _
    exact congrArg₂ (fun z w : ℂ => z * w) (unit_fourier_periodic (-n) x) (hp x)
  have hh := periodic_mean_translate _ hper a
  simp only [AddCircle.coe_add, fourier_argument_add] at hh
  unfold unitLineFourierCoeff
  rw [← intervalIntegral.integral_const_mul]
  convert hh using 1
  congr 1
  funext x
  ring

theorem unit_fourier_reciprocal_eq_one_iff (n p : ℤ) (hp : p ≠ 0) :
    fourier n ((1 / (p : ℝ) : ℝ) : AddCircle (1 : ℝ)) = 1 ↔ p ∣ n := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have ha : n • ((1 / (p : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
      ((n / (p : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_zsmul]
    congr 1
    simp only [zsmul_eq_mul, mul_one_div]
  rw [fourier_apply, ha]
  have hz : ((toCircle ((n / (p : ℝ) : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = 1 ↔
      ((n / (p : ℝ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    constructor
    · intro h
      apply injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
      rw [toCircle_zero]
      exact Subtype.ext h
    · intro h
      simp [h]
  rw [hz, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    have he : (n : ℝ) = (p : ℝ) * k := by
      simp only [zsmul_eq_mul, mul_one] at hk
      exact ((div_eq_iff hpR).mp hk.symm).trans (mul_comm _ _)
    exact ⟨k, by exact_mod_cast he⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one, Int.cast_mul]
    field_simp

/-- A genuinely smaller period kills all incompatible Fourier modes. -/
theorem unitLineFourierCoeff_zero_of_subperiod (f : ℝ → ℂ)
    (hp : Function.Periodic f 1) (p : ℤ) (hp0 : p ≠ 0)
    (hsmall : Function.Periodic f (1 / (p : ℝ))) (n : ℤ) (hn : ¬ p ∣ n) :
    unitLineFourierCoeff f n = 0 := by
  have hh := unitLineFourierCoeff_translate_identity f hp (1 / (p : ℝ)) n
  rw [show (fun x => f (x + 1 / (p : ℝ))) = f from funext hsmall] at hh
  have hn' : ¬ p ∣ -n := by simpa only [dvd_neg] using hn
  have hne : fourier (-n) ((1 / (p : ℝ) : ℝ) : AddCircle (1 : ℝ)) ≠ 1 :=
    fun h => hn' ((unit_fourier_reciprocal_eq_one_iff (-n) p hp0).mp h)
  have hz : (fourier (-n) ((1 / (p : ℝ) : ℝ) : AddCircle (1 : ℝ)) - 1) *
      unitLineFourierCoeff f n = 0 := by rw [sub_mul, one_mul, hh, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

theorem unitLineFourierCoeff_dilate_multiple (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 1) (p n : ℤ) (hp0 : p ≠ 0) :
    unitLineFourierCoeff (fun x => f ((p : ℝ) * x)) (p * n) =
      unitLineFourierCoeff f n := by
  have hper : Function.Periodic
      (fun x : ℝ => fourier (-n) (x : AddCircle (1 : ℝ)) * f x) 1 := by
    intro x
    change fourier (-n) ((x + 1 : ℝ) : AddCircle (1 : ℝ)) * f (x + 1) = _
    exact congrArg₂ (fun z w : ℂ => z * w) (unit_fourier_periodic (-n) x) (hp x)
  have hh := periodic_mean_integer_dilate _ ((unit_fourier_continuous (-n)).mul hf)
    hper p hp0
  change (∫ x in (0 : ℝ)..1,
      fourier (-n) (((p : ℝ) * x : ℝ) : AddCircle (1 : ℝ)) * f ((p : ℝ) * x)) =
    ∫ x in (0 : ℝ)..1, fourier (-n) (x : AddCircle (1 : ℝ)) * f x at hh
  simpa only [unit_fourier_integer_dilate, mul_neg, unitLineFourierCoeff] using hh

theorem unitLineFourierCoeff_dilate (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 1) (p n : ℤ) (hp0 : p ≠ 0) :
    unitLineFourierCoeff (fun x => f ((p : ℝ) * x)) n =
      if p ∣ n then unitLineFourierCoeff f (n / p) else 0 := by
  split_ifs with hn
  · obtain ⟨k, rfl⟩ := hn
    rw [Int.mul_ediv_cancel_left _ hp0]
    exact unitLineFourierCoeff_dilate_multiple f hf hp p k hp0
  · apply unitLineFourierCoeff_zero_of_subperiod _ _ p hp0 _ n hn
    · intro x
      change f ((p : ℝ) * (x + 1)) = f ((p : ℝ) * x)
      rw [mul_add, mul_one]
      simpa only [mul_one] using hp.int_mul p ((p : ℝ) * x)
    · intro x
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
      change f ((p : ℝ) * (x + 1 / (p : ℝ))) = f ((p : ℝ) * x)
      rw [mul_add, mul_one_div_cancel hpR]
      exact hp _

/-- The sum over all inverse dilation branches extracts precisely the
multiple-index Fourier integral, with the actual factor p. -/
theorem unitLineFourierCoeff_inverse_branch_sum (f : ℝ → ℂ) (hf : Continuous f)
    (p : ℕ) (hp : 0 < p) (n : ℤ) :
    unitLineFourierCoeff (fun x => ∑ a ∈ Finset.range p, f ((x + a) / p)) n =
      (p : ℂ) * unitLineFourierCoeff f ((p : ℤ) * n) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  let F : ℝ → ℂ := fun x => fourier (-((p : ℤ) * n)) (x : AddCircle (1 : ℝ)) * f x
  have hF : Continuous F := (unit_fourier_continuous _).mul hf
  have hchar (x : ℝ) (a : ℕ) :
      fourier (-((p : ℤ) * n)) (((x + a) / p : ℝ) : AddCircle (1 : ℝ)) =
        fourier (-n) (x : AddCircle (1 : ℝ)) := by
    rw [← mul_neg, ← unit_fourier_integer_dilate]
    simp only [Int.cast_natCast]
    rw [mul_div_cancel₀ _ hpR]
    simpa only [mul_one] using (unit_fourier_periodic (-n)).nat_mul a x
  have hbranch (a : ℕ) :
      unitLineFourierCoeff (fun x => f ((x + a) / p)) n =
        (p : ℂ) * ∫ x in (a : ℝ) / p..((a + 1 : ℕ) : ℝ) / p, F x := by
    have he : (fun x : ℝ => fourier (-n) (x : AddCircle (1 : ℝ)) * f ((x + a) / p)) =
        (fun x : ℝ => F ((a : ℝ) / p + x / p)) := by
      funext x
      rw [show (a : ℝ) / p + x / p = (x + a) / p by ring]
      exact (congrArg (fun z : ℂ => z * f ((x + a) / p)) (hchar x a)).symm
    rw [unitLineFourierCoeff, he, intervalIntegral.integral_comp_add_div F hpR]
    simp only [zero_div, add_zero, Complex.real_smul, Nat.cast_add, Nat.cast_one,
      Complex.ofReal_natCast]
    rw [← add_div]
  rw [unitLineFourierCoeff_sum (Finset.range p)
    (fun a x => f ((x + a) / p)) (fun a _ => hf.comp (by fun_prop))]
  simp_rw [hbranch]
  rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
    (fun a _ => hF.intervalIntegrable _ _)]
  simp only [Nat.cast_zero, zero_div, div_self hpR, F, unitLineFourierCoeff]

#print axioms fourier_argument_add
#print axioms unit_fourier_periodic
#print axioms unit_fourier_continuous
#print axioms unit_fourier_integer_dilate
#print axioms unitLineFourierCoeff_const_mul
#print axioms unitLineFourierCoeff_add
#print axioms unitLineFourierCoeff_sum
#print axioms unitLineFourierCoeff_translate_identity
#print axioms unit_fourier_reciprocal_eq_one_iff
#print axioms unitLineFourierCoeff_zero_of_subperiod
#print axioms unitLineFourierCoeff_dilate_multiple
#print axioms unitLineFourierCoeff_dilate
#print axioms unitLineFourierCoeff_inverse_branch_sum

end QuantitativeNinaMaass
