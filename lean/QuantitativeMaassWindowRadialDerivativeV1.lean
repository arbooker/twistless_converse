module

public import QuantitativeMaassPairRadialDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- A uniform quantitative radial derivative estimate for the literal squared
window profile. Its constant is chosen before radius, width, center and distance. -/
theorem windowTimeSquareProfile_radial_derivative_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ D : ℝ,0<D ∧ ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 →
      ∀ t : ℝ,1≤t → ∀ d : ℝ,0<d →
      ‖deriv (fun r => windowTimeSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR)
        (t-ε) (t+ε) (Real.cosh r)) d‖≤
        D*R^2*ε^2*(t*Real.sqrt t/Real.sqrt (Real.sinh d)+
          Real.sqrt t*Real.cosh d/(Real.sinh d*Real.sqrt (Real.sinh d))) := by
  obtain ⟨B,C,hB,hC,hbounds⟩ := windowSquareCarrier_uniform_bounds K hc 3
  let G := Real.sqrt 2/(2*Real.pi)
  have hG : 0<G := by dsimp only [G];positivity
  refine ⟨8*G*(5+2*B)*C,by positivity,?_⟩
  intro R hR ε hε hε1 t ht d hd
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have htp : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hst : 0<Real.sqrt t := Real.sqrt_pos.mpr htp
  have hs : 0<Real.sinh d := Real.sinh_pos_iff.mpr hd
  have hss : 0<Real.sqrt (Real.sinh d) := Real.sqrt_pos.mpr hs
  obtain ⟨hsA,hsB,hder⟩ := hbounds R hR ε hε hε1 t
  obtain ⟨hA,_,hBreg,_⟩ := windowSquareCarrier_regular K hc R ε t hRp
  have hpair : Function.Even (timeFrequencyShift t (windowSquareCarrierPlus K R ε t)+
      timeFrequencyShift (-t) (windowSquareCarrierMinus K R ε t)) := by
    rw [← windowTimeSquare_carriers K he hc R ε t hRp hε]
    exact timeConvolution_even _ _ (symmetricWindowTimeTest_even K he R (t-ε) (t+ε))
      (symmetricWindowTimeTest_even K he R (t-ε) (t+ε))
  have hb := even_pair_carrier_radial_bound (windowSquareCarrierPlus K R ε t)
    (windowSquareCarrierMinus K R ε t) hA hBreg (2*(B*R)) (C*R*ε^2) t d
    (by positivity) (by positivity) htp.ne' hd hsA hsB
    (fun n hn u => (hder n hn u).1) (fun n hn u => (hder n hn u).2) hpair
  rw [← windowTimeSquare_carriers K he hc R ε t hRp hε,abs_of_pos htp] at hb
  have hf1 : (t+1)^2/Real.sqrt t≤4*t*Real.sqrt t := by
    apply (div_le_iff₀ hst).mpr
    nlinarith [Real.sq_sqrt htp.le,sq_nonneg (t-1)]
  have hf2 : (t+1)/Real.sqrt t≤4*Real.sqrt t := by
    apply (div_le_iff₀ hst).mpr
    nlinarith [Real.sq_sqrt htp.le]
  have hlen : 5+2*(B*R)≤(5+2*B)*R := by nlinarith
  apply hb.trans
  calc
    _ = G*2*(5+2*(B*R))*(C*R*ε^2)*
        ((t+1)^2/Real.sqrt t/Real.sqrt (Real.sinh d)+
          ((t+1)/Real.sqrt t)*Real.cosh d/(Real.sinh d*Real.sqrt (Real.sinh d))) := by
      dsimp only [G,reciprocalSinh,reciprocalSinhSlope]
      field_simp
    _ ≤ G*2*((5+2*B)*R)*(C*R*ε^2)*
        ((4*t*Real.sqrt t)/Real.sqrt (Real.sinh d)+
          (4*Real.sqrt t)*Real.cosh d/(Real.sinh d*Real.sqrt (Real.sinh d))) := by
      gcongr
    _ = _ := by ring

#print axioms windowTimeSquareProfile_radial_derivative_bound

end QuantitativeMaass
