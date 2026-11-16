module

public import QuantitativeMaassTranslatedWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap FourierTransform
namespace QuantitativeMaass

/-- The translated window decay constant is uniform before the time shift;
its only shift loss is the explicit factor 1+abs(s). This permits growing
LV degrees, unlike a fixed-shift asymptotic statement. -/
theorem translatedWindowSquare_abel_decay_uniform (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ D : ℝ,0<D ∧ ∀ (s R ε t d : ℝ) (hR : 1≤R),0≤ε → ε≤1 → 1≤t → 0<d →
      ‖abelProfile (evenCoshLift (translatedWindowSquare K hc R (lt_of_lt_of_le zero_lt_one hR)
        (t-ε) (t+ε) s)) (Real.cosh d)‖≤D*(1+|s|)*Real.sqrt t*R^2*ε^2/Real.sqrt (Real.sinh d) := by
  obtain ⟨B,C,hB,hC,hbounds⟩ := windowSquareCarrier_uniform_bounds K hc 2
  let G : ℝ := Real.sqrt 2/(2*Real.pi)
  have hG : 0<G := by dsimp only [G];positivity
  refine ⟨G*4*(5+2*B)*C,by positivity,?_⟩
  intro s R ε t d hR hε hε1 ht hd
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have htp : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hst : 0<Real.sqrt t := Real.sqrt_pos.mpr htp
  obtain ⟨hsA,hsB,hder⟩ := hbounds R hR ε hε hε1 t
  obtain ⟨hA,_,hBreg,_⟩ := windowSquareCarrier_regular K hc R ε t hRp
  have hdecomp : translatedWindowSquare K hc R hRp (t-ε) (t+ε) s=
      timeFrequencyShift t (translatedCarrier t s (windowSquareCarrierPlus K R ε t))+
      timeFrequencyShift (-t) (translatedCarrier (-t) s (windowSquareCarrierMinus K R ε t)) := by
    unfold translatedWindowSquare
    rw [windowTimeSquare_carriers K he hc R ε t hRp hε,evenTimeTranslate_pair_carriers]
  have hpair : Function.Even (timeFrequencyShift t (translatedCarrier t s (windowSquareCarrierPlus K R ε t))+
      timeFrequencyShift (-t) (translatedCarrier (-t) s (windowSquareCarrierMinus K R ε t))) := by
    rw [← hdecomp]
    exact (translatedWindowSquare_regular K he hc R hRp (t-ε) (t+ε) s).2.1
  have hb := even_pair_carrier_abel_bound
    (translatedCarrier t s (windowSquareCarrierPlus K R ε t))
    (translatedCarrier (-t) s (windowSquareCarrierMinus K R ε t))
    (translatedCarrier_smooth t s _ hA) (translatedCarrier_smooth (-t) s _ hBreg)
    (2*(B*R)+|s|) (C*R*ε^2) t d (by positivity) (by positivity) htp.ne' hd
    (translatedCarrier_support t s (2*(B*R)) _ hsA)
    (translatedCarrier_support (-t) s (2*(B*R)) _ hsB)
    (fun n hn u => translatedCarrier_derivative_bound t s _ hA n _ (fun v => (hder n hn v).1) u)
    (fun n hn u => translatedCarrier_derivative_bound (-t) s _ hBreg n _ (fun v => (hder n hn v).2) u) hpair
  rw [← hdecomp,abs_of_pos htp] at hb
  apply hb.trans
  have hfreq : (t+1)/Real.sqrt t≤2*Real.sqrt t := by
    apply (div_le_iff₀ hst).mpr
    nlinarith [Real.sq_sqrt htp.le]
  have hlen : 4+(2*(B*R)+|s|)≤(4+2*B+|s|)*R := by
    nlinarith [mul_le_mul_of_nonneg_left hR (abs_nonneg s)]
  have hcoef : 4+2*B+|s|≤(5+2*B)*(1+|s|) := by
    nlinarith [mul_nonneg hB.le (abs_nonneg s)]
  calc
    _ = G*2*(4+(2*(B*R)+|s|))*(C*R*ε^2)*((t+1)/Real.sqrt t)/Real.sqrt (Real.sinh d) := by dsimp only [G];ring
    _ ≤ G*2*((4+2*B+|s|)*R)*(C*R*ε^2)*(2*Real.sqrt t)/Real.sqrt (Real.sinh d) := by gcongr
    _ ≤ (G*4*(5+2*B)*C)*(1+|s|)*Real.sqrt t*R^2*ε^2/Real.sqrt (Real.sinh d) := by
      have hmult := mul_le_mul_of_nonneg_right hcoef
        (show 0≤G*4*C*Real.sqrt t*R^2*ε^2/Real.sqrt (Real.sinh d) by positivity)
      convert hmult using 1 <;> ring

#print axioms translatedWindowSquare_abel_decay_uniform
end QuantitativeMaass
