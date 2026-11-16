module

public import QuantitativeMaassTranslatedTestSmoothV1
public import QuantitativeMaassCuspLogStrongRegularityV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass

theorem translatedTest_smooth (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => ψ (y-x)) := hψ.comp (contDiff_id.sub contDiff_const)

theorem translatedTest_support (ψ : ℝ → ℂ) (A B : ℝ)
    (hs : Function.support ψ⊆Icc A B) (x : ℝ) :
    Function.support (fun y => ψ (y-x))⊆Icc (x+A) (x+B) := by
  intro y hy
  have hm := hs hy
  constructor <;> linarith [hm.1,hm.2]

theorem translatedTest_second (ψ : ℝ → ℂ) (x : ℝ) :
    deriv (deriv (fun y => ψ (y-x)))=fun y => deriv (deriv ψ) (y-x) := by
  have he : deriv (fun y => ψ (y-x))=fun y => deriv ψ (y-x) :=
    funext (fun y => deriv_comp_sub_const ψ x y)
  rw [he]
  funext y
  exact deriv_comp_sub_const (deriv ψ) x y

namespace Wave

/-- Smoothing using an actual L2 state on a fixed compact log band. -/
def localCuspSmoothing (N : ℕ) (hN : 0<N) (s : SL(2,ℤ)) (A B : ℝ)
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (f : AutomorphicSpace N) (p : ℝ × ℝ) : ℂ :=
  inner ℂ (translatedLogTest A B ψ hψ p.2)
    (cuspLogConstant N hN s A B (shiftedQuotientWave N p.1 f))

/-- Joint C2 regularity is derived from actual L2-valued curves in each
variable. No regularity premise on the smoothing is assumed. -/
theorem localCuspSmoothing_contDiff_two (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    {f g : AutomorphicSpace N} (hfg : FriedrichsGraph N f g) :
    ContDiff ℝ 2 (localCuspSmoothing N hN s A B ψ hψ.continuous f) := by
  have ht : ContDiff ℝ 2 (translatedLogTest A B ψ hψ.continuous) :=
    (translatedLogTest_smooth A B ψ hψ hs).of_le (by simp)
  exact (ht.comp contDiff_snd).inner ℂ
    ((cuspLogConstant_wave_contDiff_two N hN s A B hfg).comp contDiff_fst)

theorem localCuspSmoothing_space_hasDerivAt (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    (f : AutomorphicSpace N) (t x : ℝ) :
    HasDerivAt (fun x => localCuspSmoothing N hN s A B ψ hψ.continuous f (t,x))
      (-localCuspSmoothing N hN s A B (deriv ψ) (hψ.continuous_deriv (by simp)) f (t,x)) x := by
  have h := (translatedLogTest_hasDerivAt A B ψ hψ hs x).inner ℂ
    (hasDerivAt_const x (cuspLogConstant N hN s A B (shiftedQuotientWave N t f)))
  apply h.congr_deriv
  rw [inner_zero_right,zero_add,inner_neg_left]
  rfl

theorem localCuspSmoothing_space_second (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    (f : AutomorphicSpace N) (t x : ℝ) :
    HasDerivAt (deriv (fun x => localCuspSmoothing N hN s A B ψ hψ.continuous f (t,x)))
      (localCuspSmoothing N hN s A B (deriv (deriv ψ))
        ((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp)) f (t,x)) x := by
  have hd := (contDiff_infty_iff_deriv.mp hψ).2
  have he : deriv (fun x => localCuspSmoothing N hN s A B ψ hψ.continuous f (t,x))=
      fun x => -localCuspSmoothing N hN s A B (deriv ψ) hd.continuous f (t,x) :=
    funext (fun x => (localCuspSmoothing_space_hasDerivAt N hN s A B ψ hψ hs f t x).deriv)
  rw [he]
  simpa only [neg_neg] using
    (localCuspSmoothing_space_hasDerivAt N hN s A B (deriv ψ) hd hs.deriv f t x).fun_neg

/-- The time equation is the previously derived actual weak equation,
now with a translated test whose support is contained in the fixed band. -/
theorem localCuspSmoothing_time_second (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (f : AutomorphicSpace N) (t x : ℝ)
    (hs : Function.support (fun y => ψ (y-x))⊆Icc A B) :
    HasDerivAt (deriv (fun t => localCuspSmoothing N hN s A B ψ hψ.continuous f (t,x)))
      (localCuspSmoothing N hN s A B (deriv (deriv ψ))
        ((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp)) f (t,x)) t := by
  have h := cuspLogWaveTest_second_derivative N hN s A B (fun y => ψ (y-x))
    (translatedTest_smooth ψ hψ x) hs f t
  have he := cuspLogWaveTest_congr N hN s A B _ (fun y => deriv (deriv ψ) (y-x))
    ((contDiff_infty_iff_deriv.mp (translatedTest_smooth ψ hψ x)).2.continuous_deriv (by simp))
    (((contDiff_infty_iff_deriv.mp hψ).2.continuous_deriv (by simp)).comp
      (continuous_id.sub continuous_const)) (translatedTest_second ψ x) f
  rw [he] at h
  exact h

#print axioms localCuspSmoothing_contDiff_two
#print axioms localCuspSmoothing_space_second
#print axioms localCuspSmoothing_time_second

end Wave
end QuantitativeMaass
