module

public import QuantitativeMaassBroadCarrierV1
public import QuantitativeMaassWindowAbelDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

def broadSquareCarrier (L t v : ℝ) : ℝ → ℂ :=
  carrierSquareAmplitude (broadTimeCarrier L t) (broadTimeCarrier L t) v

theorem broadSquareCarrier_smooth (L : ℝ) (hL : 0<L) (t v : ℝ) :
    ContDiff ℝ ∞ (broadSquareCarrier L t v) :=
  carrierSquareAmplitude_smooth _ _ v (broadTimeCarrier_smooth L t)
    (broadTimeCarrier_compact L hL t) (broadTimeCarrier_smooth L t)

theorem broadSquareCarrier_compact (L : ℝ) (hL : 0<L) (t v : ℝ) :
    HasCompactSupport (broadSquareCarrier L t v) :=
  carrierSquareAmplitude_compact _ _ v
    (broadTimeCarrier_compact L hL t) (broadTimeCarrier_compact L hL t)

theorem broadTimeSquare_carriers (L : ℝ) (hL : 0<L) (t : ℝ) :
    (timeConvolution (broadTimeSchwartz L hL t) (broadTimeSchwartz L hL t) : ℝ → ℂ)=
      timeFrequencyShift t (broadSquareCarrier L t (-2*t))+
      timeFrequencyShift (-t) (broadSquareCarrier L t (2*t)) := by
  rw [timeConvolution_eq_function,broadTimeSchwartz_coe,broadTimeWeight_carriers]
  exact timeFunctionConvolution_pair_square _ _ t (broadTimeCarrier_smooth L t)
    (broadTimeCarrier_compact L hL t) (broadTimeCarrier_smooth L t)
    (broadTimeCarrier_compact L hL t)

/-- Uniform derivative cost for the genuine broad convolution square.
The frequency in the second convolution factor is never differentiated. -/
theorem broadSquareCarrier_bounds (m : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ L : ℝ,1≤L → ∀ t v : ℝ,
      Function.support (broadSquareCarrier L t v) ⊆ Icc (-2:ℝ) 2 ∧
      ∀ n : ℕ,n≤m → ∀ s : ℝ,
        ‖iteratedDeriv n (broadSquareCarrier L t v) s‖≤C*L^(2*(m+1)) := by
  obtain ⟨C,hC,hb⟩ := broadTimeCarrier_derivative_bounds m
  refine ⟨4*C^2,by positivity,?_⟩
  intro L hL t v
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hs : Function.support (broadTimeCarrier L t) ⊆ Icc (-1:ℝ) 1 := by
    apply (broadTimeCarrier_support L hLp t).trans
    have hdiv : 1/L≤1 := (div_le_one hLp).mpr hL
    exact Icc_subset_Icc (by linarith) hdiv
  refine ⟨?_,?_⟩
  · simpa only [mul_one,broadSquareCarrier] using carrierSquareAmplitude_support _ _ v 1 hs hs
  · intro n hn s
    have hz (u : ℝ) : ‖broadTimeCarrier L t u‖≤C*L^(m+1) := by
      simpa only [iteratedDeriv_zero] using hb L hL t 0 (Nat.zero_le _) u
    have hh := carrierSquareAmplitude_derivative_bound _ _ 1 (C*L^(m+1))
      (by norm_num) (broadTimeCarrier_smooth L t) (broadTimeCarrier_compact L hLp t)
      (broadTimeCarrier_smooth L t) hs n hz (hb L hL t n hn) hz v s
    apply hh.trans_eq
    rw [mul_pow,← pow_mul]
    ring

/-- The squared broad packet has the required square-root-frequency
off-diagonal decay, with only polynomial cost in its broad width. -/
theorem broadTimeSquare_abel_decay :
    ∃ C : ℝ,0≤C ∧ ∀ (L t d : ℝ) (hL : 1≤L),1≤t → 0<d →
      ‖abelProfile (evenCoshLift (timeConvolution
        (broadTimeSchwartz L (lt_of_lt_of_le zero_lt_one hL) t)
        (broadTimeSchwartz L (lt_of_lt_of_le zero_lt_one hL) t))) (Real.cosh d)‖≤
      C*Real.sqrt t*L^6/Real.sqrt (Real.sinh d) := by
  obtain ⟨C,hC,hb⟩ := broadSquareCarrier_bounds 2
  let G := Real.sqrt 2/(2*Real.pi)
  have hG : 0≤G := by dsimp only [G]; positivity
  refine ⟨24*G*C,by positivity,?_⟩
  intro L t d hL ht hd
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have htp : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hp := hb L hL t (-2*t)
  have hm := hb L hL t (2*t)
  have he : Function.Even (timeFrequencyShift t (broadSquareCarrier L t (-2*t))+
      timeFrequencyShift (-t) (broadSquareCarrier L t (2*t))) := by
    rw [← broadTimeSquare_carriers L hLp t]
    exact timeConvolution_even _ _ (broadTimeWeight_even L t) (broadTimeWeight_even L t)
  have hh := even_pair_carrier_abel_bound _ _ (broadSquareCarrier_smooth L hLp t (-2*t))
    (broadSquareCarrier_smooth L hLp t (2*t)) 2 (C*L^6) t d
    (by norm_num) (by positivity) htp.ne' hd hp.1 hm.1 hp.2 hm.2 he
  rw [← broadTimeSquare_carriers L hLp t,abs_of_pos htp] at hh
  have hfreq : (t+1)/Real.sqrt t≤2*Real.sqrt t := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr htp)).mpr
    nlinarith [Real.sq_sqrt htp.le]
  apply hh.trans
  calc
    _ = (12*G*C*L^6)*((t+1)/Real.sqrt t)/Real.sqrt (Real.sinh d) := by
      dsimp only [G]
      ring
    _ ≤ (12*G*C*L^6)*(2*Real.sqrt t)/Real.sqrt (Real.sinh d) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfreq (by positivity)) (by positivity)
    _ = _ := by ring

#print axioms broadTimeSquare_carriers
#print axioms broadSquareCarrier_bounds
#print axioms broadTimeSquare_abel_decay

end QuantitativeMaass
