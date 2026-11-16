module

public import QuantitativeMaassWindowSquareCarrierV1
public import QuantitativeMaassAbelOscillatoryAmplitudeV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The amplitude obtained after one derivative of a modulated carrier. -/
def timeDerivativeCarrier (t : ℝ) (A : ℝ → ℂ) (u : ℝ) : ℂ :=
  (t:ℂ)*Complex.I*A u+deriv A u

theorem timeDerivativeCarrier_smooth (t : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (timeDerivativeCarrier t A) := by
  have hd := (contDiff_infty_iff_deriv.mp hA).2
  unfold timeDerivativeCarrier
  fun_prop

theorem timeFrequencyShift_deriv (t : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) :
    deriv (timeFrequencyShift t A)=timeFrequencyShift t (timeDerivativeCarrier t A) := by
  funext u
  have he := ((((hasDerivAt_id u).const_mul t).ofReal_comp).mul_const Complex.I).cexp
  have hh := he.mul ((hA.differentiable (by simp)).differentiableAt.hasDerivAt)
  have hfun : ((fun x : ℝ => Complex.exp ((t*id x:ℝ)*Complex.I))*A)=timeFrequencyShift t A := by
    funext x
    rfl
  rw [hfun] at hh
  rw [hh.deriv]
  simp only [timeFrequencyShift,timeDerivativeCarrier,id_eq,mul_one]
  ring

theorem timeDerivativeCarrier_deriv (t : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) :
    deriv (timeDerivativeCarrier t A)=fun u => (t:ℂ)*Complex.I*deriv A u+iteratedDeriv 2 A u := by
  funext u
  have h1 := (hA.differentiable (by simp)).differentiableAt.hasDerivAt (x:=u)
  have h2 := (((contDiff_infty_iff_deriv.mp hA).2).differentiable (by simp)).differentiableAt.hasDerivAt (x:=u)
  have hh := ((h1.const_mul ((t:ℂ)*Complex.I)).add h2).deriv
  have hfun : ((fun y => (t:ℂ)*Complex.I*A y)+deriv A)=timeDerivativeCarrier t A := by
    funext y
    rfl
  rw [hfun] at hh
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh

theorem timeDerivativeCarrier_bounds (t : ℝ) (A : ℝ → ℂ) (M : ℝ)
    (hA : ContDiff ℝ ∞ A) (hM : ∀ n : ℕ,n≤2 → ∀ u,‖iteratedDeriv n A u‖≤M) :
    ∀ u,‖timeDerivativeCarrier t A u‖≤(|t|+1)*M ∧
      ‖deriv (timeDerivativeCarrier t A) u‖≤(|t|+1)*M := by
  have h0 (u) : ‖A u‖≤M := by simpa only [iteratedDeriv_zero] using hM 0 (by omega) u
  have h1 (u) : ‖deriv A u‖≤M := by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hM 1 (by omega) u
  have hb (z w : ℂ) (hz : ‖z‖≤M) (hw : ‖w‖≤M) : ‖(t:ℂ)*Complex.I*z+w‖≤(|t|+1)*M := by
    calc
      _ ≤ ‖(t:ℂ)*Complex.I*z‖+‖w‖ := norm_add_le _ _
      _ = |t| *‖z‖+‖w‖ := by simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
      _ ≤ |t| *M+M := add_le_add (mul_le_mul_of_nonneg_left hz (abs_nonneg t)) hw
      _ = _ := by ring
  intro u
  constructor
  · exact hb (A u) (deriv A u) (h0 u) (h1 u)
  · rw [timeDerivativeCarrier_deriv t A hA]
    exact hb (deriv A u) (iteratedDeriv 2 A u) (h1 u) (hM 2 le_rfl u)

theorem timeDerivativeCarrier_support (t : ℝ) (A : ℝ → ℂ) (L : ℝ)
    (hs : Function.support A⊆Icc (-L) L) :
    Function.support (timeDerivativeCarrier t A)⊆Icc (-L) L := by
  have hd : Function.support (deriv A)⊆Icc (-L) L :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Icc)
  intro u hu
  by_contra hn
  have h0 : A u=0 := by by_contra hh;exact hn (hs hh)
  have h1 : deriv A u=0 := by by_contra hh;exact hn (hd hh)
  exact hu (by simp only [timeDerivativeCarrier,h0,h1,mul_zero,add_zero])

/-- Compact support turns the literal halfline integral into a finite interval,
without discarding the singular endpoint by an unproved limiting argument. -/
theorem time_halfline_integral_restrict (g : ℝ → ℂ) (d b : ℝ) (hdb : d≤b)
    (hz : ∀ u,b<u → g u=0) : (∫ u in Ioi d,g u)=∫ u in d..b,g u := by
  rw [intervalIntegral.integral_of_le hdb]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro u hu
  apply hz u
  by_contra hn
  exact hu.2 ⟨hu.1,le_of_not_gt hn⟩

/-- The scalar decay estimate applied to the derivative of a genuine smooth
carrier. The amplitude cost is derived from its first two derivatives. -/
theorem timeDerivativeCarrier_oscillatory_bound (A : ℝ → ℂ) (hA : ContDiff ℝ ∞ A)
    (L M d b t : ℝ) (hd : 0<d) (hdb : d≤b) (hlen : b-d≤L) (ht : t≠0)
    (hM0 : 0≤M) (hM : ∀ n : ℕ,n≤2 → ∀ u,‖iteratedDeriv n A u‖≤M) :
    ‖∫ u in d..b,timeFrequencyShift t (timeDerivativeCarrier t A) u*
      (abelSingularWeight d u:ℂ)‖≤
      (4+L)*((|t|+1)*M)/(Real.sqrt |t| *Real.sqrt (Real.sinh d)) := by
  have hg := timeDerivativeCarrier_smooth t A hA
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hb := timeDerivativeCarrier_bounds t A M hA hM
  have hh := abelSingularWeight_amplitude_decay (timeDerivativeCarrier t A)
    (deriv (timeDerivativeCarrier t A)) d b t ((|t|+1)*M) ((|t|+1)*M)
    hd hdb ht (by positivity) (by positivity) hg.continuous.measurable
    (fun u _ => (hg.differentiable (by simp)).differentiableAt.hasDerivAt)
    (hg'.continuous.intervalIntegrable d b) (fun u _ => (hb u).1) (fun u _ => (hb u).2)
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hlen (show 0≤(|t|+1)*M by positivity)]

/-- An even sum of two compact smooth carriers has the actual Abel-profile
bound furnished by the two derived oscillatory estimates. -/
theorem even_pair_carrier_abel_bound (A B : ℝ → ℂ) (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (L M t d : ℝ) (hL : 0≤L) (hM : 0≤M)
    (ht : t≠0) (hd : 0<d)
    (hsA : Function.support A⊆Icc (-L) L) (hsB : Function.support B⊆Icc (-L) L)
    (hbA : ∀ n : ℕ,n≤2 → ∀ u,‖iteratedDeriv n A u‖≤M)
    (hbB : ∀ n : ℕ,n≤2 → ∀ u,‖iteratedDeriv n B u‖≤M)
    (he : Function.Even (timeFrequencyShift t A+timeFrequencyShift (-t) B)) :
    ‖abelProfile (evenCoshLift (timeFrequencyShift t A+timeFrequencyShift (-t) B))
      (Real.cosh d)‖≤
      (Real.sqrt 2/(2*Real.pi))*(2*(4+L)*((|t|+1)*M)/
        (Real.sqrt |t| *Real.sqrt (Real.sinh d))) := by
  let f := timeFrequencyShift t A+timeFrequencyShift (-t) B
  have hf : ContDiff ℝ ∞ f := (timeFrequencyShift_smooth t A hA).add
    (timeFrequencyShift_smooth (-t) B hB)
  have hfs : Function.support f⊆Icc (-L) L := by
    intro u hu
    by_contra hn
    have h0 : A u=0 := by by_contra hh;exact hn (hsA hh)
    have h1 : B u=0 := by by_contra hh;exact hn (hsB hh)
    exact hu (by simp only [f,Pi.add_apply,timeFrequencyShift,h0,h1,mul_zero,add_zero])
  have hfc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc (fun u hu => by
    by_contra hh;exact hu (hfs hh))
  have hds : Function.support (deriv f)⊆Icc (-L) L :=
    support_deriv_subset.trans (closure_minimal hfs isClosed_Icc)
  have hder : deriv f=timeFrequencyShift t (timeDerivativeCarrier t A)+
      timeFrequencyShift (-t) (timeDerivativeCarrier (-t) B) := by
    rw [show deriv f=deriv (timeFrequencyShift t A)+deriv (timeFrequencyShift (-t) B) from
      funext (fun u => deriv_add
        ((timeFrequencyShift_smooth t A hA).differentiable (by simp)).differentiableAt
        ((timeFrequencyShift_smooth (-t) B hB).differentiable (by simp)).differentiableAt),
      timeFrequencyShift_deriv t A hA,timeFrequencyShift_deriv (-t) B hB]
  let b := max d L
  have hdb : d≤b := le_max_left _ _
  have hlen : b-d≤L := by dsimp only [b];rcases max_cases d L with h|h <;> rw [h.1] <;> linarith
  have hrestrict := time_halfline_integral_restrict
    (fun u => deriv f u/(Real.sqrt (Real.cosh u-Real.cosh d):ℂ)) d b hdb (by
      intro u hu
      have hz : deriv f u=0 := by
        by_contra hn
        have hh := (hds hn).2
        have hLb : L≤b := le_max_right _ _
        linarith
      simp only [hz,zero_div])
  let gp := timeDerivativeCarrier t A
  let gm := timeDerivativeCarrier (-t) B
  have hp := timeDerivativeCarrier_smooth t A hA
  have hm := timeDerivativeCarrier_smooth (-t) B hB
  have hip : IntervalIntegrable (fun u => timeFrequencyShift t gp u*(abelSingularWeight d u:ℂ)) volume d b :=
    abelSingularWeight_amplitude_integrable gp d b t ((|t|+1)*M) hd hdb
      hp.continuous.measurable (fun u _ => (timeDerivativeCarrier_bounds t A M hA hbA u).1)
  have him : IntervalIntegrable (fun u => timeFrequencyShift (-t) gm u*(abelSingularWeight d u:ℂ)) volume d b :=
    abelSingularWeight_amplitude_integrable gm d b (-t) ((|-t|+1)*M) hd hdb
      hm.continuous.measurable (fun u _ => (timeDerivativeCarrier_bounds (-t) B M hB hbB u).1)
  have heq : (∫ u in d..b,deriv f u/(Real.sqrt (Real.cosh u-Real.cosh d):ℂ))=
      (∫ u in d..b,timeFrequencyShift t gp u*(abelSingularWeight d u:ℂ))+
      (∫ u in d..b,timeFrequencyShift (-t) gm u*(abelSingularWeight d u:ℂ)) := by
    rw [← intervalIntegral.integral_add hip him]
    apply intervalIntegral.integral_congr
    intro u _
    rw [hder]
    simp only [Pi.add_apply,abelSingularWeight,abelRadiusTimeCoordinate,Complex.ofReal_inv,
      gp,gm,div_eq_mul_inv,add_mul]
  have hb1 := timeDerivativeCarrier_oscillatory_bound A hA L M d b t hd hdb hlen ht hM hbA
  have hb2 := timeDerivativeCarrier_oscillatory_bound B hB L M d b (-t) hd hdb hlen (neg_ne_zero.mpr ht) hM hbB
  rw [abs_neg] at hb2
  have hsum := (norm_add_le _ _).trans (add_le_add hb1 hb2)
  change ‖abelProfile (evenCoshLift f) (Real.cosh d)‖≤_
  rw [abelProfile_evenCoshLift_cosh f hf he hfc d hd.le,hrestrict,heq,norm_mul,norm_neg]
  have hnorm : ‖(Real.sqrt 2/(2*Real.pi):ℂ)‖=Real.sqrt 2/(2*Real.pi) := by
    rw [← Complex.ofReal_ofNat,← Complex.ofReal_mul,← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  convert hsum using 1
  ring

/-- Uniform off-diagonal decay of the ORIGINAL window-square Abel profile.
The constant is chosen before scale, width, spectral center and displacement. -/
theorem windowTimeSquare_abel_decay (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ D : ℝ,0<D ∧ ∀ (R ε t d : ℝ) (hR : 1≤R),0≤ε → ε≤1 → 1≤t → 0<d →
      ‖abelProfile (evenCoshLift (timeConvolution
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε))
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε))))
        (Real.cosh d)‖≤D*Real.sqrt t*R^2*ε^2/Real.sqrt (Real.sinh d) := by
  obtain ⟨B,C,hB,hC,hbounds⟩ := windowSquareCarrier_uniform_bounds K hc 2
  let G : ℝ := Real.sqrt 2/(2*Real.pi)
  have hG : 0<G := by dsimp only [G];positivity
  refine ⟨G*4*(4+2*B)*C,by positivity,?_⟩
  intro R ε t d hR hε hε1 ht hd
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have htp : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hst : 0<Real.sqrt t := Real.sqrt_pos.mpr htp
  obtain ⟨hsA,hsB,hder⟩ := hbounds R hR ε hε hε1 t
  obtain ⟨hA,hAc,hBreg,hBc⟩ := windowSquareCarrier_regular K hc R ε t hRp
  have hpair : Function.Even (timeFrequencyShift t (windowSquareCarrierPlus K R ε t)+
      timeFrequencyShift (-t) (windowSquareCarrierMinus K R ε t)) := by
    rw [← windowTimeSquare_carriers K he hc R ε t hRp hε]
    exact timeConvolution_even _ _ (symmetricWindowTimeTest_even K he R (t-ε) (t+ε))
      (symmetricWindowTimeTest_even K he R (t-ε) (t+ε))
  have hb := even_pair_carrier_abel_bound (windowSquareCarrierPlus K R ε t)
    (windowSquareCarrierMinus K R ε t) hA hBreg (2*(B*R)) (C*R*ε^2) t d
    (by positivity) (by positivity) htp.ne' hd hsA hsB
    (fun n hn u => (hder n hn u).1) (fun n hn u => (hder n hn u).2) hpair
  rw [← windowTimeSquare_carriers K he hc R ε t hRp hε,abs_of_pos htp] at hb
  apply hb.trans
  have hfreq : (t+1)/Real.sqrt t≤2*Real.sqrt t := by
    apply (div_le_iff₀ hst).mpr
    nlinarith [Real.sq_sqrt htp.le]
  have hlen : 4+2*(B*R)≤(4+2*B)*R := by nlinarith
  calc
    _ = G*2*(4+2*(B*R))*(C*R*ε^2)*((t+1)/Real.sqrt t)/Real.sqrt (Real.sinh d) := by dsimp only [G];ring
    _ ≤ G*2*((4+2*B)*R)*(C*R*ε^2)*(2*Real.sqrt t)/Real.sqrt (Real.sinh d) := by
      gcongr
    _ = _ := by ring

#print axioms windowTimeSquare_abel_decay

#print axioms timeDerivativeCarrier_smooth
#print axioms timeFrequencyShift_deriv
#print axioms timeDerivativeCarrier_deriv
#print axioms timeDerivativeCarrier_bounds
#print axioms timeDerivativeCarrier_support
#print axioms time_halfline_integral_restrict
#print axioms timeDerivativeCarrier_oscillatory_bound
#print axioms even_pair_carrier_abel_bound

end QuantitativeMaass
