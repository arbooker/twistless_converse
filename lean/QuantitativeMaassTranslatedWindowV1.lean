module

public import QuantitativeMaassTimeTranslateCarrierV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Actual symmetric time translate of the original window square. -/
def translatedWindowSquare (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b s : ℝ) : ℝ → ℂ :=
  evenTimeTranslate s (timeConvolution (windowTimeSchwartz K hc R hR a b)
    (windowTimeSchwartz K hc R hR a b))

theorem translatedWindowSquare_regular (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b s : ℝ) :
    ContDiff ℝ ∞ (translatedWindowSquare K hc R hR a b s) ∧
    Function.Even (translatedWindowSquare K hc R hR a b s) ∧
    HasCompactSupport (translatedWindowSquare K hc R hR a b s) ∧
    ∀ u,star (translatedWindowSquare K hc R hR a b s u)=translatedWindowSquare K hc R hR a b s u := by
  let f := windowTimeSchwartz K hc R hR a b
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R a b
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R a b hR
  have hfr : ∀ u,star (f u)=f u := symmetricWindowTimeTest_real K he R a b
  exact ⟨evenTimeTranslate_smooth s _ ((timeConvolution f f).smooth ⊤),
    evenTimeTranslate_even s _ (timeConvolution_even f f hfe hfe),
    evenTimeTranslate_compact s _ (timeConvolution_compact f f hfc hfc),
    evenTimeTranslate_real s _ (timeConvolution_real f f hfr hfr)⟩

/-- A single support constant works before all radii, endpoints and translations. -/
theorem translatedWindowSquare_uniform_support (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ U : ℝ,0<U ∧ ∀ (R : ℝ) (hR : 0<R) (a b s : ℝ),
      Function.support (translatedWindowSquare K hc R hR a b s)⊆
        Icc (-(2*(U*R)+|s|)) (2*(U*R)+|s|) := by
  obtain ⟨U,hU,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  refine ⟨U,hU,?_⟩
  intro R hR a b s
  apply evenTimeTranslate_support
  simpa only [two_mul] using timeConvolution_support
    (windowTimeSchwartz K hc R hR a b) (windowTimeSchwartz K hc R hR a b)
    (U*R) (U*R) (hs R hR a b) (hs R hR a b)

theorem translatedWindowSquare_profile_continuous (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b s : ℝ) :
    ContinuousOn (abelProfile (evenCoshLift (translatedWindowSquare K hc R hR a b s))) (Ici 1) := by
  have hh := translatedWindowSquare_regular K he hc R hR a b s
  exact evenTime_abel_continuous _ hh.1 hh.2.1 hh.2.2.1

/-- Off-diagonal oscillatory decay of the actual translated window square.
The constant depends on the fixed time translation, and is chosen before
scale, width, spectral centre and geometric displacement. -/
theorem translatedWindowSquare_abel_decay (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (s : ℝ) :
    ∃ D : ℝ,0<D ∧ ∀ (R ε t d : ℝ) (hR : 1≤R),0≤ε → ε≤1 → 1≤t → 0<d →
      ‖abelProfile (evenCoshLift (translatedWindowSquare K hc R (lt_of_lt_of_le zero_lt_one hR)
        (t-ε) (t+ε) s)) (Real.cosh d)‖≤D*Real.sqrt t*R^2*ε^2/Real.sqrt (Real.sinh d) := by
  obtain ⟨B,C,hB,hC,hbounds⟩ := windowSquareCarrier_uniform_bounds K hc 2
  let G : ℝ := Real.sqrt 2/(2*Real.pi)
  have hG : 0<G := by dsimp only [G];positivity
  refine ⟨G*4*(4+2*B+|s|)*C,by positivity,?_⟩
  intro R ε t d hR hε hε1 ht hd
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
  calc
    _ = G*2*(4+(2*(B*R)+|s|))*(C*R*ε^2)*((t+1)/Real.sqrt t)/Real.sqrt (Real.sinh d) := by dsimp only [G];ring
    _ ≤ G*2*((4+2*B+|s|)*R)*(C*R*ε^2)*(2*Real.sqrt t)/Real.sqrt (Real.sinh d) := by gcongr
    _ = _ := by ring

#print axioms translatedWindowSquare_regular
#print axioms translatedWindowSquare_uniform_support
#print axioms translatedWindowSquare_profile_continuous
#print axioms translatedWindowSquare_abel_decay

end QuantitativeMaass
