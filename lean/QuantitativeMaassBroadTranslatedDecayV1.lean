module

public import QuantitativeMaassBroadSquareCarrierV1
public import QuantitativeMaassTimeTranslateCarrierV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- Cosine translation of the broad square retains square-root spectral
decay uniformly before the translation, width and central frequency. -/
theorem broadTranslatedSquare_abel_decay :
    ∃ C : ℝ,0≤C ∧ ∀ (L t τ d : ℝ) (hL : 1≤L),1≤t → 0<d →
      ‖abelProfile (evenCoshLift (evenTimeTranslate τ
        (timeConvolution (broadTimeSchwartz L (lt_of_lt_of_le zero_lt_one hL) t)
          (broadTimeSchwartz L (lt_of_lt_of_le zero_lt_one hL) t)))) (Real.cosh d)‖≤
      C*(1+|τ|)*Real.sqrt t*L^6/Real.sqrt (Real.sinh d) := by
  obtain ⟨C,hC,hb⟩ := broadSquareCarrier_bounds 2
  let G := Real.sqrt 2/(2*Real.pi)
  have hG : 0≤G := by dsimp only [G]; positivity
  refine ⟨24*G*C,by positivity,?_⟩
  intro L t τ d hL ht hd
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have htp : 0<t := lt_of_lt_of_le zero_lt_one ht
  let A := broadSquareCarrier L t (-2*t)
  let B := broadSquareCarrier L t (2*t)
  have hA := broadSquareCarrier_smooth L hLp t (-2*t)
  have hB := broadSquareCarrier_smooth L hLp t (2*t)
  have hp := hb L hL t (-2*t)
  have hm := hb L hL t (2*t)
  have he : Function.Even (timeFrequencyShift t (translatedCarrier t τ A)+
      timeFrequencyShift (-t) (translatedCarrier (-t) τ B)) := by
    rw [← evenTimeTranslate_pair_carriers]
    change Function.Even (evenTimeTranslate τ
      (timeFrequencyShift t (broadSquareCarrier L t (-2*t))+
        timeFrequencyShift (-t) (broadSquareCarrier L t (2*t))))
    rw [← broadTimeSquare_carriers L hLp t]
    exact evenTimeTranslate_even τ _
      (timeConvolution_even _ _ (broadTimeWeight_even L t) (broadTimeWeight_even L t))
  have hh := even_pair_carrier_abel_bound _ _
    (translatedCarrier_smooth t τ A hA) (translatedCarrier_smooth (-t) τ B hB)
    (2+|τ|) (C*L^6) t d (by positivity) (by positivity) htp.ne' hd
    (translatedCarrier_support t τ 2 A hp.1) (translatedCarrier_support (-t) τ 2 B hm.1)
    (fun n hn u => translatedCarrier_derivative_bound t τ A hA n _ (hp.2 n hn) u)
    (fun n hn u => translatedCarrier_derivative_bound (-t) τ B hB n _ (hm.2 n hn) u) he
  rw [← evenTimeTranslate_pair_carriers,abs_of_pos htp] at hh
  change ‖abelProfile (evenCoshLift (evenTimeTranslate τ
    (timeFrequencyShift t (broadSquareCarrier L t (-2*t))+
      timeFrequencyShift (-t) (broadSquareCarrier L t (2*t))))) (Real.cosh d)‖≤_ at hh
  rw [← broadTimeSquare_carriers L hLp t] at hh
  have hfreq : (t+1)/Real.sqrt t≤2*Real.sqrt t := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr htp)).mpr
    nlinarith [Real.sq_sqrt htp.le]
  have hlen : 4+(2+|τ|)≤6*(1+|τ|) := by linarith [abs_nonneg τ]
  apply hh.trans
  calc
    _ = G*2*(4+(2+|τ|))*(C*L^6)*((t+1)/Real.sqrt t)/Real.sqrt (Real.sinh d) := by
      dsimp only [G]
      ring
    _ ≤ G*2*(6*(1+|τ|))*(C*L^6)*(2*Real.sqrt t)/Real.sqrt (Real.sinh d) := by
      gcongr
    _ = _ := by ring

#print axioms broadTranslatedSquare_abel_decay

end QuantitativeMaass
