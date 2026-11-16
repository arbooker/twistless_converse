module

public import QuantitativeMaassRadialCarrierDecayV1
public import QuantitativeMaassAbelRadialDerivativeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The radial differentiated integrand is exactly the derived carrier. -/
theorem radialTimeCarrier_expression (A : ℝ → ℂ) (hA : ContDiff ℝ ∞ A) (t u : ℝ) :
    deriv (deriv (timeFrequencyShift t A)) u/(Real.sinh u:ℂ)-
      deriv (timeFrequencyShift t A) u*(Real.cosh u:ℂ)/(Real.sinh u:ℂ)^2=
      timeFrequencyShift t (radialTimeCarrier t A) u := by
  rw [timeFrequencyShift_deriv t A hA,
    timeFrequencyShift_deriv t (timeDerivativeCarrier t A) (timeDerivativeCarrier_smooth t A hA)]
  simp only [timeFrequencyShift,radialTimeCarrier,reciprocalSinh,reciprocalSinhSlope,
    Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_pow]
  ring

/-- Explicit off-diagonal derivative bound for an even pair of compact
modulated carriers. It controls the actual Abel profile rather than a model. -/
theorem even_pair_carrier_radial_bound (A B : ℝ → ℂ) (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (L M t d : ℝ) (hL : 0≤L) (hM : 0≤M)
    (ht : t≠0) (hd : 0<d)
    (hsA : Function.support A⊆Icc (-L) L) (hsB : Function.support B⊆Icc (-L) L)
    (hbA : ∀ n : ℕ,n≤3 → ∀ u,‖iteratedDeriv n A u‖≤M)
    (hbB : ∀ n : ℕ,n≤3 → ∀ u,‖iteratedDeriv n B u‖≤M)
    (he : Function.Even (timeFrequencyShift t A+timeFrequencyShift (-t) B)) :
    ‖deriv (fun r => abelProfile (evenCoshLift (timeFrequencyShift t A+timeFrequencyShift (-t) B))
        (Real.cosh r)) d‖≤
      (Real.sqrt 2/(2*Real.pi))*Real.sinh d*
        (2*(5+L)*M*((|t|+1)^2*reciprocalSinh d+(|t|+1)*reciprocalSinhSlope d)/
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
  have hdds : Function.support (deriv (deriv f))⊆Icc (-L) L :=
    support_deriv_subset.trans (closure_minimal hds isClosed_Icc)
  have hder : deriv f=deriv (timeFrequencyShift t A)+deriv (timeFrequencyShift (-t) B) :=
    funext (fun u => deriv_add
      ((timeFrequencyShift_smooth t A hA).differentiable (by simp)).differentiableAt
      ((timeFrequencyShift_smooth (-t) B hB).differentiable (by simp)).differentiableAt)
  have hder2 : deriv (deriv f)=deriv (deriv (timeFrequencyShift t A))+deriv (deriv (timeFrequencyShift (-t) B)) := by
    rw [hder]
    exact funext (fun u => deriv_add
      (((contDiff_infty_iff_deriv.mp (timeFrequencyShift_smooth t A hA)).2).differentiable (by simp)).differentiableAt
      (((contDiff_infty_iff_deriv.mp (timeFrequencyShift_smooth (-t) B hB)).2).differentiable (by simp)).differentiableAt)
  let b := max d L
  have hdb : d≤b := le_max_left _ _
  have hlen : b-d≤L := by dsimp only [b];rcases max_cases d L with h|h <;> rw [h.1] <;> linarith
  have hrestrict := time_halfline_integral_restrict
    (fun u => (deriv (deriv f) u/(Real.sinh u:ℂ)-deriv f u*(Real.cosh u:ℂ)/(Real.sinh u:ℂ)^2)/
      (Real.sqrt (Real.cosh u-Real.cosh d):ℂ)) d b hdb (by
      intro u hu
      have hz : deriv f u=0 := by
        by_contra hn
        have hh := (hds hn).2
        have hLb : L≤b := le_max_right _ _
        linarith
      have hz2 : deriv (deriv f) u=0 := by
        by_contra hn
        have hh := (hdds hn).2
        have hLb : L≤b := le_max_right _ _
        linarith
      simp only [hz,hz2,zero_div,zero_mul,sub_zero])
  have hp := radialTimeCarrier_abel_decay A hA d b L t M hd hdb hlen ht hM hbA
  have hm := radialTimeCarrier_abel_decay B hB d b L (-t) M hd hdb hlen (neg_ne_zero.mpr ht) hM hbB
  have hex (u : ℝ) :
      (deriv (deriv f) u/(Real.sinh u:ℂ)-deriv f u*(Real.cosh u:ℂ)/(Real.sinh u:ℂ)^2)/
        (Real.sqrt (Real.cosh u-Real.cosh d):ℂ)=
      timeFrequencyShift t (radialTimeCarrier t A) u*(abelSingularWeight d u:ℂ)+
        timeFrequencyShift (-t) (radialTimeCarrier (-t) B) u*(abelSingularWeight d u:ℂ) := by
    rw [hder2,hder]
    simp only [Pi.add_apply]
    rw [← radialTimeCarrier_expression A hA t u,← radialTimeCarrier_expression B hB (-t) u]
    simp only [abelSingularWeight,abelRadiusTimeCoordinate,Complex.ofReal_inv]
    ring
  have heq : (∫ u in d..b,
      (deriv (deriv f) u/(Real.sinh u:ℂ)-deriv f u*(Real.cosh u:ℂ)/(Real.sinh u:ℂ)^2)/
        (Real.sqrt (Real.cosh u-Real.cosh d):ℂ))=
      (∫ u in d..b,timeFrequencyShift t (radialTimeCarrier t A) u*(abelSingularWeight d u:ℂ))+
        (∫ u in d..b,timeFrequencyShift (-t) (radialTimeCarrier (-t) B) u*(abelSingularWeight d u:ℂ)) := by
    rw [← intervalIntegral.integral_add hp.1 hm.1]
    exact intervalIntegral.integral_congr (fun u _ => hex u)
  rw [abs_neg] at hm
  have hbound := (norm_add_le _ _).trans (add_le_add hp.2 hm.2)
  have hnorm : ‖(Real.sqrt 2/(2*Real.pi):ℂ)‖=Real.sqrt 2/(2*Real.pi) := by
    rw [← Complex.ofReal_ofNat 2,← Complex.ofReal_mul,← Complex.ofReal_div,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  change ‖deriv (fun r => abelProfile (evenCoshLift f) (Real.cosh r)) d‖≤_
  rw [abelProfile_evenCoshLift_radial_deriv f hf he hfc d hd,hrestrict,heq,
    norm_mul,norm_mul,norm_neg,hnorm,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.sinh_pos_iff.mpr hd)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  convert hbound using 1
  ring

#print axioms radialTimeCarrier_expression
#print axioms even_pair_carrier_radial_bound

end QuantitativeMaass
