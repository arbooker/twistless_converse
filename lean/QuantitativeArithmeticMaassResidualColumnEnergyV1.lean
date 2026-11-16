module

public import QuantitativeArithmeticMaassResidualIntegralV1
public import QuantitativeMaassCylinderSquareKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Integrating the identity/remainder decomposition only over a finite
centre region; no finite-volume assertion about the cylinder is used. -/
theorem radialIntegralKernel_norm_integral_bound (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det)
    (g : ℝ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support g ⊆ Iic (Real.cosh R)) (o : ℍ) (L D E : ℝ)
    (hD : 0 ≤ D) (hd : ‖g 1‖ ≤ D)
    (hi : IntegrableOn (radialIntegralRemainder N M hM g) (Metric.closedBall o L))
    (hb : (∫ z in Metric.closedBall o L, ‖radialIntegralRemainder N M hM g z‖) ≤ E) :
    IntegrableOn (fun z => radialPoincareKernel N g z (positiveIntegralGL M hM • z))
      (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L, ‖radialPoincareKernel N g z
      (positiveIntegralGL M hM • z)‖) ≤ volume.real (Metric.closedBall o L)*D+E := by
  classical
  let c : ℂ := if integralIdentityCoset N M then g 1 else 0
  have hc : ‖c‖ ≤ D := by
    dsimp only [c]
    split_ifs
    · exact hd
    · simpa using hD
  have hic : IntegrableOn (fun _z : ℍ => c) (Metric.closedBall o L) :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall o L)
  have hsplit (z : ℍ) : radialPoincareKernel N g z (positiveIntegralGL M hM • z) =
      c + radialIntegralRemainder N M hM g z :=
    radialIntegralKernel_identity_split N M hM g R hR hs z
  have hik : IntegrableOn (fun z => radialPoincareKernel N g z
      (positiveIntegralGL M hM • z)) (Metric.closedBall o L) :=
    (hic.add hi).congr (Filter.Eventually.of_forall (fun z => (hsplit z).symm))
  refine ⟨hik,?_⟩
  calc
    _ ≤ ∫ z in Metric.closedBall o L, ‖c‖ + ‖radialIntegralRemainder N M hM g z‖ := by
      apply integral_mono_ae hik.norm (hic.norm.add hi.norm)
      exact Filter.Eventually.of_forall (fun z => by
        dsimp only [Pi.add_apply]
        rw [hsplit]
        exact norm_add_le _ _)
    _ = volume.real (Metric.closedBall o L)*‖c‖ +
        ∫ z in Metric.closedBall o L, ‖radialIntegralRemainder N M hM g z‖ := by
      rw [integral_add hic.norm hi.norm]
      simp [measureReal_def]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hc ENNReal.toReal_nonneg) hb

theorem spectralResidualSchwartz_real (t : ℝ) (f : SchwartzMap ℝ ℂ)
    (hr : ∀ s, star (f s) = f s) :
    ∀ s, star (spectralResidualSchwartz t f s) = spectralResidualSchwartz t f s := by
  have hd := deriv_real_profile f hr
  have hdd := deriv_real_profile (deriv f) hd
  intro s
  change star (-deriv (deriv f) s - (t : ℂ)^2*f s) = _
  have ht : star ((t : ℂ)^2) = (t : ℂ)^2 := by simp
  rw [star_sub, star_neg, star_mul, hdd s, ht, hr s]
  change -deriv (deriv f) s - f s*(t : ℂ)^2 =
    -deriv (deriv f) s - (t : ℂ)^2*f s
  ring

/-- The integrated residual profile controls the squared norm of the
actual residual column, pointwise, before any spectral cutoff is applied. -/
theorem spectralResidualColumn_norm_square (t : ℝ) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ s, star (f s) = f s) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Icc (-R) R) (z : ℍ) :
    ‖cylinderTimeColumn (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f hc) (spectralResidualSchwartz_even t f he)
      R hR (spectralTimeResidual_support t f R hs) z‖^2 =
      (radialPoincareKernel 0 (abelProfile (evenCoshLift
        (spectralTimeResidual t (spectralTimeResidual t (timeConvolution f f))))) z z).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), cylinderTimeSquare_kernel_cross
    (spectralResidualSchwartz t f) _ _ (spectralResidualSchwartz_real t f hr),
    spectralResidualSchwartz_abel_square t f he hc]
  rfl

/-- Residual column energy on a finite propagated centre region. The
identity term is O(t³ ε); the nonidentity term is the integrated oscillatory
bound. In particular this never integrates over the whole infinite cylinder. -/
theorem windowResidualColumn_integrated_energy (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1) :
    ∃ U C : ℝ, ∃ hU : 0 < U, 0 < C ∧ ∀ (o : ℍ) (L R t ε : ℝ)
      (hR : 1 ≤ R), 1 ≤ t → 0 ≤ ε → ε ≤ 1 →
      let f := windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε)
      ∃ (hs : Function.support f ⊆ Icc (-(U*R)) (U*R)),
      (∫ z in Metric.closedBall o L,
        ‖cylinderTimeColumn (spectralResidualSchwartz t f)
          (spectralResidualSchwartz_compact t f
            (symmetricWindowTimeTest_compact K hc R t (t+ε) (lt_of_lt_of_le zero_lt_one hR)))
          (spectralResidualSchwartz_even t f (symmetricWindowTimeTest_even K he R t (t+ε)))
          (U*R) (by positivity) (spectralTimeResidual_support t f (U*R) hs) z‖^2) ≤
        volume.real (Metric.closedBall o L)*
          ((576*(1+∫ x, |x|^5*K x)/(4*Real.pi))*t^3*ε)+
        (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (2*(U*R)+2*L) : ℝ)*
          (C*t^2*Real.sqrt t*R^2*ε^2)*
          (Real.pi*(volume.real (Metric.closedBall o L)+
            hyperbolicSublevelConstant o L (2*(U*R)+2*L+2*Real.log 2))) := by
  obtain ⟨U,hU,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hdecay⟩ := windowResidualSquare_abel_decay K he hc
  refine ⟨U,C,hU,hC,?_⟩
  intro o L R t ε hR ht hε hε1
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let f := windowTimeSchwartz K hc R hRp t (t+ε)
  have hfs : Function.support f ⊆ Icc (-(U*R)) (U*R) := hs R hRp t (t+ε)
  refine ⟨hfs,?_⟩
  let g := windowResidualSquareProfile K hc R hRp t ε
  have hcs : Function.support (timeConvolution f f : ℝ → ℂ) ⊆
      Icc (-(2*(U*R))) (2*(U*R)) := by
    simpa only [two_mul] using timeConvolution_support f f (U*R) (U*R) hfs hfs
  have hgs : Function.support g ⊆ Iic (Real.cosh (2*(U*R))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity)
      (spectralTimeResidual_support t _ _ (spectralTimeResidual_support t _ _ hcs)))
  have hId : 0 < (1 : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  have hact (z : ℍ) : positiveIntegralGL 1 hId • z = z := by
    apply UpperHalfPlane.ext
    rw [positiveIntegralGL_fractional]
    simp
  have hentry : ∀ i j : Fin 2, |((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)| ≤ 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  obtain ⟨hi,hb⟩ := radialIntegralRemainder_all_integral_bound 0 1 hId 1 (by norm_num)
    hentry o L (2*(U*R)) (by positivity) g
    (windowResidualSquareProfile_continuous K he hc R hRp t ε) hgs
    (C*t^2*Real.sqrt t*R^2*ε^2) (by positivity)
    (fun d hd => hdecay R ε t d hR hε hε1 ht hd)
  simp only [hact, dist_self, add_zero, mul_one] at hb
  have hmoment : 0 ≤ ∫ x, |x|^5*K x := integral_nonneg (fun x => mul_nonneg (pow_nonneg (abs_nonneg x) 5) (hK x))
  have hD : 0 ≤ (576*(1+∫ x, |x|^5*K x)/(4*Real.pi))*t^3*ε := by positivity
  obtain ⟨hki,hkb⟩ := radialIntegralKernel_norm_integral_bound 0 1 hId g
    (2*(U*R)) (by positivity) hgs o L _ _ hD
    (windowResidualSquare_diagonal_bound K he hc hK hm R t ε hR ht hε hε1) hi hb
  simp only [hact] at hki hkb
  have heq (z : ℍ) := spectralResidualColumn_norm_square t f
    (symmetricWindowTimeTest_compact K hc R t (t+ε) hRp)
    (symmetricWindowTimeTest_even K he R t (t+ε))
    (symmetricWindowTimeTest_real K he R t (t+ε)) (U*R) (by positivity) hfs z
  calc
    _ = ∫ z in Metric.closedBall o L, (radialPoincareKernel 0 g z z).re := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall heq
    _ ≤ ∫ z in Metric.closedBall o L, ‖radialPoincareKernel 0 g z z‖ :=
      integral_mono_ae hki.re hki.norm
        (Filter.Eventually.of_forall (fun z => Complex.re_le_norm _))
    _ ≤ _ := hkb

#print axioms radialIntegralKernel_norm_integral_bound
#print axioms spectralResidualColumn_norm_square
#print axioms windowResidualColumn_integrated_energy

end QuantitativeMaass
