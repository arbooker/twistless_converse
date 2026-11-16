module

public import QuantitativeMaassTimeResidualCarrierV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Applying the spectral residual twice costs two powers of the frequency,
not four, after demodulating at the actual window centre. -/
theorem timeResidualCarrier_twice_iterated_bound (t τ : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (m : ℕ) (M : ℝ)
    (hb : ∀ n : ℕ, n ≤ m+4 → ∀ s, ‖iteratedDeriv n A s‖ ≤ M) :
    ∀ n : ℕ, n ≤ m → ∀ s,
      ‖iteratedDeriv n (timeResidualCarrier t τ (timeResidualCarrier t τ A)) s‖ ≤
        (|τ^2-t^2| + 2*|τ| + 1)^2*M := by
  have hfirst := timeResidualCarrier_iterated_bound t τ A hA (m+2) M
    (by simpa only [Nat.add_assoc] using hb)
  have hsecond := timeResidualCarrier_iterated_bound t τ (timeResidualCarrier t τ A)
    (timeResidualCarrier_smooth t τ A hA) m
    ((|τ^2-t^2| + 2*|τ| + 1)*M) hfirst
  intro n hn s
  convert hsecond n hn s using 1
  ring

/-- The differential operator corresponding to the spectral multiplier r²−t². -/
def spectralTimeResidual (t : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun s => -deriv (deriv f) s - (t : ℂ)^2*f s

theorem spectralTimeResidual_smooth (t : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (spectralTimeResidual t f) := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 := (contDiff_infty_iff_deriv.mp hf1).2
  unfold spectralTimeResidual
  fun_prop

theorem spectralTimeResidual_even (t : ℝ) (f : ℝ → ℂ)
    (he : Function.Even f) : Function.Even (spectralTimeResidual t f) := by
  have h2 := even_time_second_deriv_even f he
  intro s
  simp only [spectralTimeResidual, h2 s, he s]

theorem spectralTimeResidual_add (t : ℝ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    spectralTimeResidual t (f+g) = spectralTimeResidual t f + spectralTimeResidual t g := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hg1 := (contDiff_infty_iff_deriv.mp hg).2
  have hsum : deriv (f+g) = deriv f + deriv g := by
    funext s
    exact deriv_add ((hf.differentiable (by simp)).differentiableAt)
      ((hg.differentiable (by simp)).differentiableAt)
  have hsum2 : deriv (deriv (f+g)) = deriv (deriv f) + deriv (deriv g) := by
    rw [hsum]
    funext s
    exact deriv_add ((hf1.differentiable (by simp)).differentiableAt)
      ((hg1.differentiable (by simp)).differentiableAt)
  funext s
  simp only [spectralTimeResidual, hsum2, Pi.add_apply]
  ring

theorem spectralTimeResidual_pair (t τ : ℝ) (A B : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    spectralTimeResidual t (timeFrequencyShift τ A + timeFrequencyShift (-τ) B) =
      timeFrequencyShift τ (timeResidualCarrier t τ A) +
      timeFrequencyShift (-τ) (timeResidualCarrier t (-τ) B) := by
  rw [spectralTimeResidual_add t _ _ (timeFrequencyShift_smooth τ A hA)
    (timeFrequencyShift_smooth (-τ) B hB)]
  exact congrArg₂ (· + ·) (timeFrequencyShift_residual t τ A hA)
    (timeFrequencyShift_residual t (-τ) B hB)

/-- The squared residual multiplier of a positive convolution square retains
an exact two-carrier decomposition. -/
theorem spectralTimeResidual_twice_pair (t τ : ℝ) (A B : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    spectralTimeResidual t (spectralTimeResidual t
      (timeFrequencyShift τ A + timeFrequencyShift (-τ) B)) =
      timeFrequencyShift τ (timeResidualCarrier t τ (timeResidualCarrier t τ A)) +
      timeFrequencyShift (-τ) (timeResidualCarrier t (-τ) (timeResidualCarrier t (-τ) B)) := by
  rw [spectralTimeResidual_pair t τ A B hA hB,
    spectralTimeResidual_pair t τ _ _ (timeResidualCarrier_smooth t τ A hA)
      (timeResidualCarrier_smooth t (-τ) B hB)]

/-- Uniform support and derivative bounds for the residual-square carriers of
an actual one-sided window [t,t+ε]. The two residuals are centred at t, whereas
the oscillatory phases are centred at ±(t+ε/2). -/
theorem windowResidualSquareCarrier_uniform_bounds (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) (m : ℕ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ t : ℝ, 1 ≤ t →
      let A := timeResidualCarrier t (t+ε/2) (timeResidualCarrier t (t+ε/2)
        (windowSquareCarrierPlus K R (ε/2) (t+ε/2)))
      let B' := timeResidualCarrier t (-(t+ε/2)) (timeResidualCarrier t (-(t+ε/2))
        (windowSquareCarrierMinus K R (ε/2) (t+ε/2)))
      Function.support A ⊆ Icc (-(2*(B*R))) (2*(B*R)) ∧
      Function.support B' ⊆ Icc (-(2*(B*R))) (2*(B*R)) ∧
      ∀ n : ℕ, n ≤ m → ∀ s : ℝ,
        ‖iteratedDeriv n A s‖ ≤ C*t^2*R*ε^2 ∧
        ‖iteratedDeriv n B' s‖ ≤ C*t^2*R*ε^2 := by
  obtain ⟨B,C,hB,hC,hbounds⟩ := windowSquareCarrier_uniform_bounds K hc (m+4)
  refine ⟨B,36*C,hB,by positivity,?_⟩
  intro R hR ε hε hε1 t ht
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hhalf : 0 ≤ ε/2 := by positivity
  have hhalf1 : ε/2 ≤ 1 := by linarith
  obtain ⟨hsA,hsB,hder⟩ := hbounds R hR (ε/2) hhalf hhalf1 (t+ε/2)
  obtain ⟨hA,_,hBreg,_⟩ := windowSquareCarrier_regular K hc R (ε/2) (t+ε/2) hRp
  refine ⟨timeResidualCarrier_support _ _ _ _
      (timeResidualCarrier_support _ _ _ _ hsA),
    timeResidualCarrier_support _ _ _ _ (timeResidualCarrier_support _ _ _ _ hsB), ?_⟩
  intro n hn s
  have hbplus := timeResidualCarrier_twice_iterated_bound t (t+ε/2)
    (windowSquareCarrierPlus K R (ε/2) (t+ε/2)) hA m (C*R*(ε/2)^2)
    (fun j hj u => (hder j hj u).1) n hn s
  have hbminus := timeResidualCarrier_twice_iterated_bound t (-(t+ε/2))
    (windowSquareCarrierMinus K R (ε/2) (t+ε/2)) hBreg m (C*R*(ε/2)^2)
    (fun j hj u => (hder j hj u).2) n hn s
  have hp := timeResidualCarrier_window_coefficient t ε ht hε hε1
  have hm := timeResidualCarrier_negative_window_coefficient t ε ht hε hε1
  have hbound (τ : ℝ) (hb : |τ^2-t^2|+2*|τ|+1 ≤ 6*t) :
      (|τ^2-t^2|+2*|τ|+1)^2*(C*R*(ε/2)^2) ≤ (36*C)*t^2*R*ε^2 := by
    calc
      _ ≤ (6*t)^2*(C*R*(ε/2)^2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hb 2) (by positivity)
      _ ≤ (36*C)*t^2*R*ε^2 := by
        nlinarith [mul_nonneg (show 0 ≤ C*R*t^2 by positivity) (sq_nonneg ε)]
  exact ⟨hbplus.trans (hbound _ hp), hbminus.trans (hbound _ hm)⟩

/-- Off-diagonal decay for the actual window-square residual. The multiplier
is (r²−t²)² times the original squared window, and the bound loses only t²
relative to the unweighted window square. -/
theorem windowResidualSquare_abel_decay (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ)))) :
    ∃ D : ℝ, 0 < D ∧ ∀ (R ε t d : ℝ) (hR : 1 ≤ R),
      0 ≤ ε → ε ≤ 1 → 1 ≤ t → 0 < d →
      ‖abelProfile (evenCoshLift (spectralTimeResidual t (spectralTimeResidual t
        (timeConvolution (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε))
          (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε))))))
        (Real.cosh d)‖ ≤ D*t^2*Real.sqrt t*R^2*ε^2/Real.sqrt (Real.sinh d) := by
  obtain ⟨B,C,hB,hC,hbounds⟩ := windowResidualSquareCarrier_uniform_bounds K hc 2
  let G : ℝ := Real.sqrt 2/(2*Real.pi)
  have hG : 0 < G := by dsimp only [G]; positivity
  refine ⟨G*6*(4+2*B)*C, by positivity, ?_⟩
  intro R ε t d hR hε hε1 ht hd
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hhalf : 0 ≤ ε/2 := by positivity
  let τ := t+ε/2
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  let A0 := windowSquareCarrierPlus K R (ε/2) τ
  let B0 := windowSquareCarrierMinus K R (ε/2) τ
  let A := timeResidualCarrier t τ (timeResidualCarrier t τ A0)
  let B' := timeResidualCarrier t (-τ) (timeResidualCarrier t (-τ) B0)
  obtain ⟨hA0,_,hB0,_⟩ := windowSquareCarrier_regular K hc R (ε/2) τ hRp
  have hA : ContDiff ℝ ∞ A := timeResidualCarrier_smooth t τ _
    (timeResidualCarrier_smooth t τ _ hA0)
  have hB' : ContDiff ℝ ∞ B' := timeResidualCarrier_smooth t (-τ) _
    (timeResidualCarrier_smooth t (-τ) _ hB0)
  have hends0 : τ-ε/2=t := by dsimp only [τ]; ring
  have hends1 : τ+ε/2=t+ε := by dsimp only [τ]; ring
  have hpair := windowTimeSquare_carriers K he hc R (ε/2) τ hRp hhalf
  rw [hends0,hends1] at hpair
  have hres := congrArg (fun f => spectralTimeResidual t (spectralTimeResidual t f)) hpair
  rw [spectralTimeResidual_twice_pair t τ _ _ hA0 hB0] at hres
  have he0 := timeConvolution_even
    (windowTimeSchwartz K hc R hRp t (t+ε)) (windowTimeSchwartz K hc R hRp t (t+ε))
    (symmetricWindowTimeTest_even K he R t (t+ε))
    (symmetricWindowTimeTest_even K he R t (t+ε))
  have hepair : Function.Even (timeFrequencyShift τ A+timeFrequencyShift (-τ) B') := by
    rw [← hres]
    exact spectralTimeResidual_even t _ (spectralTimeResidual_even t _ he0)
  obtain ⟨hsA,hsB,hder⟩ := hbounds R hR ε hε hε1 t ht
  have hb := even_pair_carrier_abel_bound A B' hA hB' (2*(B*R)) (C*t^2*R*ε^2) τ d
    (by positivity) (by positivity) hτ.ne' hd hsA hsB
    (fun n hn s => (hder n hn s).1) (fun n hn s => (hder n hn s).2) hepair
  rw [← hres, abs_of_pos hτ] at hb
  apply hb.trans
  have hfreq : (τ+1)/Real.sqrt τ ≤ 3*Real.sqrt t := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hτ)).mpr
    have hle : t ≤ τ := by dsimp only [τ]; linarith
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle)
      (show 0 ≤ 3*Real.sqrt t by positivity)
    have hsq := Real.sq_sqrt ht0.le
    dsimp only [τ] at *
    nlinarith
  have hlen : 4+2*(B*R) ≤ (4+2*B)*R := by nlinarith
  calc
    _ = G*2*(4+2*(B*R))*(C*t^2*R*ε^2)*((τ+1)/Real.sqrt τ)/
        Real.sqrt (Real.sinh d) := by dsimp only [G]; ring
    _ ≤ G*2*((4+2*B)*R)*(C*t^2*R*ε^2)*(3*Real.sqrt t)/
        Real.sqrt (Real.sinh d) := by gcongr
    _ = _ := by ring

#print axioms windowResidualSquare_abel_decay

#print axioms timeResidualCarrier_twice_iterated_bound
#print axioms spectralTimeResidual_twice_pair
#print axioms windowResidualSquareCarrier_uniform_bounds

end QuantitativeMaass
