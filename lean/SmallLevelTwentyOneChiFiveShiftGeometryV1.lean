module

public import SmallLevelTwentyOneChiFiveDenominatorV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex SmallLevelTwentyOneChiFiveObstruction

theorem exceptional_root_line {f : ℕ → ℂ}
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) {s : ℂ}
    (hs : denominator 2 f s=0) : s.re=1 ∧ s.im≠0 := by
  obtain ⟨_,_,hi,hn⟩ := exceptional_denominator_root ha hs
  have hnorm := Complex.norm_natCast_cpow_of_pos (by decide : 0<2) (s-1)
  norm_num only [Nat.cast_ofNat,sub_re,one_re] at hnorm
  rw [hn] at hnorm
  have hr : s.re-1=0 := by
    apply (Real.rpow_right_inj (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)).mp
    simpa only [Real.rpow_zero] using hnorm.symm
  refine ⟨by linarith,?_⟩
  intro him
  apply hi
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    show Complex.log (2:ℂ)=(Real.log 2:ℂ) by norm_cast]
  simp only [Complex.exp_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,
    Complex.sub_im,Complex.one_im,him,sub_zero,mul_zero,zero_mul,add_zero,Real.sin_zero]

theorem shifted_two (s : ℂ) (n : ℕ) :
    (2:ℂ)^(s+(n:ℂ)-1)=(2:ℂ)^n*(2:ℂ)^(s-1) := by
  rw [show s+(n:ℂ)-1=(n:ℂ)+(s-1) by ring,
    Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),Complex.cpow_natCast]

/-- The determinant obstruction is nonzero at every rightward integer
shift of an exceptional denominator root. -/
theorem shifted_obstruction_nonzero {f : ℕ → ℂ}
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) {s : ℂ}
    (hs : denominator 2 f s=0) (n : ℕ) :
    ((2:ℂ)^(s+(n:ℂ)-1))^2-1≠0 ∧
      residual ((2:ℂ)^(s+(n:ℂ)-1)) ((3:ℂ)^(s+(n:ℂ)-1))≠0 := by
  obtain ⟨hu,_,huim,hunorm⟩ := exceptional_denominator_root ha hs
  have hline := (exceptional_root_line ha hs).1
  have hy : ‖(3:ℂ)^(s+(n:ℂ)-1)‖=(3:ℝ)^n := by
    have h := Complex.norm_natCast_cpow_of_pos (by decide : 0<3) (s+(n:ℂ)-1)
    simpa only [Nat.cast_ofNat,sub_re,add_re,natCast_re,one_re,hline,
      show (1:ℝ)+(n:ℝ)-1=(n:ℝ) by ring,Real.rpow_natCast] using h
  constructor
  · intro he
    have hx : ((2:ℂ)^(s+(n:ℂ)-1)).im≠0 := by
      rw [shifted_two]
      rw [show (2:ℂ)^n=(((2:ℝ)^n:ℝ):ℂ) by norm_cast]
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,add_zero] using mul_ne_zero (pow_ne_zero n (by norm_num : (2:ℝ)≠0)) huim
    have hsq : ((2:ℂ)^(s+(n:ℂ)-1))^2=1 := sub_eq_zero.mp he
    have hfactors : ((2:ℂ)^(s+(n:ℂ)-1)-1)*((2:ℂ)^(s+(n:ℂ)-1)+1)=0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfactors with h|h
    · have hr := sub_eq_zero.mp h
      exact hx (by rw [hr]; simp)
    · have hr : (2:ℂ)^(s+(n:ℂ)-1)= -1 := by linear_combination h
      exact hx (by rw [hr]; simp)
  · rw [shifted_two]
    simpa only [Complex.ofReal_ofNat] using residual_nonzero n hu hunorm hy

#print axioms exceptional_root_line
#print axioms shifted_obstruction_nonzero
end SmallLevelTwentyOneChiFive
