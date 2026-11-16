module

public import QuantitativeArithmeticMaassResidualColumnEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Uniform O_K(t ε) source diagonal once the smoothing scale resolves
the window. This retains the window width in the leading bound. -/
theorem windowIdentityContribution_resolved_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R t ε : ℝ) (hR : 1 ≤ R),
      1 ≤ t → 0 ≤ ε → ε ≤ 1 → 1/R ≤ ε →
      ‖windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε)‖ ≤ C*t*ε := by
  let m₁ := ∫ x, |x| * K x
  let m₂ := ∫ x, |x|^2*K x
  have h₁ : 0 ≤ m₁ := integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (hK x))
  have h₂ : 0 ≤ m₂ := integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hK x))
  refine ⟨(5+24*m₁+8*m₂)/(4*Real.pi),by positivity,?_⟩
  intro R t ε hR ht hε hε1 hresolve
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have htp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let I := windowIdentityContribution K hc R hRp t (t+ε)
  have hb := windowIdentityContribution_error K he hc hK hm R hRp t (t+ε) htp (by linarith)
  have hn := norm_le_norm_sub_add ((4*Real.pi : ℂ)*I) (((t+ε)^2-t^2 : ℝ) : ℂ)
  have hcoef : ‖(4*Real.pi : ℂ)‖ = 4*Real.pi := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hmain : ‖(((t+ε)^2-t^2 : ℝ) : ℂ)‖ = (t+ε)^2-t^2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
  rw [norm_mul, hcoef, hmain] at hn
  have hfirst : 8*(1+(t+ε))*m₁/R ≤ 24*m₁*t*ε := by
    calc
      _ = (8*(1+(t+ε))*m₁)*(1/R) := by ring
      _ ≤ (8*(1+(t+ε))*m₁)*ε := mul_le_mul_of_nonneg_left hresolve (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg h₁ hε]
  have hinv : 1/R ≤ 1 := (div_le_one hRp).mpr hR
  have hsecond : 8*m₂/R^2 ≤ 8*m₂*t*ε := by
    have hsq : (1/R)^2 ≤ ε := by
      have hnon : 0 ≤ 1/R := by positivity
      nlinarith
    calc
      _ = 8*m₂*(1/R)^2 := by ring
      _ ≤ 8*m₂*ε := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg h₂ hε]
  have htotal : (4*Real.pi)*‖I‖ ≤ (5+24*m₁+8*m₂)*t*ε := by
    change ‖(4*Real.pi : ℂ)*I-(((t+ε)^2-t^2 : ℝ) : ℂ)‖ ≤
      8*(1+(t+ε))*m₁/R+8*m₂/R^2+2*((t+ε)-t) at hb
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hε1), mul_le_mul_of_nonneg_right ht hε]
  apply (le_div_iff₀ (show 0 < 4*Real.pi by positivity)).mpr
    (show ‖I‖*(4*Real.pi) ≤ (5+24*m₁+8*m₂)*t*ε by nlinarith) |>.trans_eq ?_
  ring

/-- Finite-centre source-column energy from the diagonal and off-diagonal
profile bounds, with the cylinder geometry explicit. -/
theorem cylinderTimeColumn_integrated_energy (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ s, star (f s) = f s) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Icc (-R) R) (o : ℍ) (L C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hd : ‖abelProfile (evenCoshLift (timeConvolution f f)) 1‖ ≤ D)
    (hb : ∀ d : ℝ, 0 < d →
      ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖ ≤
        C/Real.sqrt (Real.sinh d)) :
    (∫ z in Metric.closedBall o L, ‖cylinderTimeColumn f hc he R hR hs z‖^2) ≤
      volume.real (Metric.closedBall o L)*D+
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (2*R+2*L) : ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+
          hyperbolicSublevelConstant o L (2*R+2*L+2*Real.log 2))) := by
  let g := abelProfile (evenCoshLift (timeConvolution f f))
  have hg : ContinuousOn g (Ici 1) := evenTime_abel_continuous _
    ((timeConvolution f f).smooth ⊤) (timeConvolution_even f f he he)
    (timeConvolution_compact f f hc hc)
  have hcs : Function.support (timeConvolution f f : ℝ → ℂ) ⊆ Icc (-(2*R)) (2*R) := by
    simpa only [two_mul] using timeConvolution_support f f R R hs hs
  have hgs : Function.support g ⊆ Iic (Real.cosh (2*R)) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hcs)
  have hId : 0 < (1 : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  have hact (z : ℍ) : positiveIntegralGL 1 hId • z = z := by
    apply UpperHalfPlane.ext
    rw [positiveIntegralGL_fractional]
    simp
  have hentry : ∀ i j : Fin 2, |((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)| ≤ 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  obtain ⟨hi,hrem⟩ := radialIntegralRemainder_all_integral_bound 0 1 hId 1 (by norm_num)
    hentry o L (2*R) (by positivity) g hg hgs C hC hb
  simp only [hact, dist_self, add_zero, mul_one] at hrem
  obtain ⟨hki,hbound⟩ := radialIntegralKernel_norm_integral_bound 0 1 hId g
    (2*R) (by positivity) hgs o L D _ hD hd hi hrem
  simp only [hact] at hki hbound
  calc
    _ = ∫ z in Metric.closedBall o L, (radialPoincareKernel 0 g z z).re := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), cylinderTimeSquare_kernel_cross f hc he hr R hR hs]
      rfl
    _ ≤ ∫ z in Metric.closedBall o L, ‖radialPoincareKernel 0 g z z‖ :=
      integral_mono_ae hki.re hki.norm
        (Filter.Eventually.of_forall (fun z => Complex.re_le_norm _))
    _ ≤ _ := hbound

theorem oneSidedWindowSquare_abel_decay (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R ε t d : ℝ) (hR : 1 ≤ R),
      0 ≤ ε → ε ≤ 1 → 1 ≤ t → 0 < d →
      ‖abelProfile (evenCoshLift (timeConvolution
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε))
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε))))
          (Real.cosh d)‖ ≤ C*Real.sqrt t*R^2*ε^2/Real.sqrt (Real.sinh d) := by
  obtain ⟨C,hC,hb⟩ := windowTimeSquare_abel_decay K he hc
  refine ⟨2*C,by positivity,?_⟩
  intro R ε t d hR hε hε1 ht hd
  have hhalf : 0 ≤ ε/2 := by positivity
  have hτ : 1 ≤ t+ε/2 := by linarith
  have hh := hb R (ε/2) (t+ε/2) d hR hhalf (by linarith) hτ hd
  rw [show t+ε/2-ε/2=t by ring, show t+ε/2+ε/2=t+ε by ring] at hh
  have hs : Real.sqrt (t+ε/2) ≤ 2*Real.sqrt t := by
    have ht0 : 0 ≤ t := by linarith
    have hτ0 : 0 ≤ t+ε/2 := by linarith
    nlinarith [Real.sq_sqrt ht0, Real.sq_sqrt hτ0,
      Real.sqrt_nonneg t, Real.sqrt_nonneg (t+ε/2)]
  apply hh.trans
  calc
    _ ≤ C*(2*Real.sqrt t)*R^2*ε^2/Real.sqrt (Real.sinh d) := by
      gcongr
      linarith
    _ = _ := by ring

/-- Complete source-energy companion to the residual-energy theorem,
for the same literal one-sided window and finite centre balls. -/
theorem windowSourceColumn_integrated_energy (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1) :
    ∃ U C D : ℝ, ∃ hU : 0 < U, 0 < C ∧ 0 < D ∧ ∀ (o : ℍ) (L R t ε : ℝ)
      (hR : 1 ≤ R), 1 ≤ t → 0 ≤ ε → ε ≤ 1 → 1/R ≤ ε →
      let f := windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε)
      ∃ (hs : Function.support f ⊆ Icc (-(U*R)) (U*R)),
      (∫ z in Metric.closedBall o L, ‖cylinderTimeColumn f
        (symmetricWindowTimeTest_compact K hc R t (t+ε) (lt_of_lt_of_le zero_lt_one hR))
        (symmetricWindowTimeTest_even K he R t (t+ε)) (U*R) (by positivity) hs z‖^2) ≤
        volume.real (Metric.closedBall o L)*(D*t*ε)+
        (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (2*(U*R)+2*L) : ℝ)*
          (C*Real.sqrt t*R^2*ε^2)*
          (Real.pi*(volume.real (Metric.closedBall o L)+
            hyperbolicSublevelConstant o L (2*(U*R)+2*L+2*Real.log 2))) := by
  obtain ⟨U,hU,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hdecay⟩ := oneSidedWindowSquare_abel_decay K he hc
  obtain ⟨D,hD,hdiag⟩ := windowIdentityContribution_resolved_bound K he hc hK hm
  refine ⟨U,C,D,hU,hC,hD,?_⟩
  intro o L R t ε hR ht hε hε1 hresolve
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let f := windowTimeSchwartz K hc R hRp t (t+ε)
  have hfs : Function.support f ⊆ Icc (-(U*R)) (U*R) := hs R hRp t (t+ε)
  refine ⟨hfs,?_⟩
  exact cylinderTimeColumn_integrated_energy f
    (symmetricWindowTimeTest_compact K hc R t (t+ε) hRp)
    (symmetricWindowTimeTest_even K he R t (t+ε))
    (symmetricWindowTimeTest_real K he R t (t+ε)) (U*R) (by positivity) hfs o L
    (C*Real.sqrt t*R^2*ε^2) (D*t*ε) (by positivity) (by positivity)
    (hdiag R t ε hR ht hε hε1 hresolve)
    (fun d hd => hdecay R ε t d hR hε hε1 ht hd)

#print axioms windowIdentityContribution_resolved_bound
#print axioms cylinderTimeColumn_integrated_energy
#print axioms oneSidedWindowSquare_abel_decay
#print axioms windowSourceColumn_integrated_energy

end QuantitativeMaass
