module

public import FinitenessOriginalFrickeV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPairedMellin

open Complex MeasureTheory FinitenessFiniteOrder FinitenessBoundaryDecay
  FinitenessMellinContour FinitenessMellinSeries FinitenessDirichletInversion

/-- The right boundary of the dual series supplies the left boundary of
the first series. This is a two-function functional equation. -/
theorem reflected_pair {F G : ℂ → ℂ} {σ κ : ℝ} {ε : ℂ}
    (hG : Rapid G σ) (hε : ‖ε‖ = 1)
    (hFE : ∀ z, F z = ε*G ((κ : ℂ)-z)) : Rapid F (κ-σ) := by
  intro n
  obtain ⟨C₀,h0⟩ := hG 0
  obtain ⟨Cₙ,hn⟩ := hG n
  refine ⟨2^(n-1)*(|κ|^n*C₀+Cₙ), ?_⟩
  intro z hz
  have hw : ((κ : ℂ)-z).re=σ := by simp only [sub_re,ofReal_re,hz]; ring
  have he : ‖F z‖=‖G ((κ : ℂ)-z)‖ := by rw [hFE,norm_mul,hε,one_mul]
  have hnorm : ‖z‖ ≤ |κ|+‖(κ : ℂ)-z‖ := by
    calc
      ‖z‖ = ‖(κ : ℂ)-((κ : ℂ)-z)‖ := by congr 1; ring
      _ ≤ ‖(κ : ℂ)‖+‖(κ : ℂ)-z‖ := norm_sub_le _ _
      _ = _ := by rw [Complex.norm_real,Real.norm_eq_abs]
  have hp : ‖z‖^n ≤ 2^(n-1)*(|κ|^n+‖(κ : ℂ)-z‖^n) :=
    (pow_le_pow_left₀ (norm_nonneg _) hnorm n).trans
      (add_pow_le (abs_nonneg κ) (norm_nonneg _) n)
  have hh0 : ‖G ((κ : ℂ)-z)‖ ≤ C₀ := by simpa using h0 _ hw
  have hhn := hn _ hw
  rw [he]
  calc
    _ ≤ (2^(n-1)*(|κ|^n+‖(κ : ℂ)-z‖^n))*‖G ((κ : ℂ)-z)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = 2^(n-1)*(|κ|^n*‖G ((κ : ℂ)-z)‖+‖(κ : ℂ)-z‖^n*‖G ((κ : ℂ)-z)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hh0 (by positivity)) hhn) (by positivity)

theorem contour_inversion_pair {F G : ℂ → ℂ}
    (hhol : Differentiable ℂ F) (hF : Bound F)
    {c κ : ℝ} (hc : κ-c < c) (hrF : Rapid F c) (hrG : Rapid G c)
    {ε : ℂ} (hε : ‖ε‖=1) (hFE : ∀ z, F z=ε*G ((κ : ℂ)-z)) (l : ℝ) :
    integral F c l = ε*Complex.exp ((-l*κ : ℝ):ℂ)*integral G c (-l) := by
  have hl := reflected_pair hrG hε hFE
  rw [← integral_eq hhol hF hc hl hrF l]
  have he (t : ℝ) : kernel F l (((κ-c : ℝ):ℂ)+(t : ℂ)*I) =
      (ε*Complex.exp ((-l*κ : ℝ):ℂ))*kernel G (-l) ((c : ℂ)+((-t : ℝ):ℂ)*I) := by
    have hz : (κ : ℂ)-(((κ-c : ℝ):ℂ)+(t : ℂ)*I)=
        (c : ℂ)+((-t : ℝ):ℂ)*I := by push_cast; ring
    rw [kernel,hFE,hz,kernel]
    have hp : ((-l : ℝ):ℂ)*(((κ-c : ℝ):ℂ)+(t : ℂ)*I)=
        ((-l*κ : ℝ):ℂ)+((-(-l) : ℝ):ℂ)*((c : ℂ)+((-t : ℝ):ℂ)*I) := by
      push_cast; ring
    rw [hp,Complex.exp_add]
    ring
  change (∫ t : ℝ, kernel F l (((κ-c : ℝ):ℂ)+(t : ℂ)*I)) = _
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  exact MeasureTheory.integral_neg_eq_self
    (fun t : ℝ => kernel G (-l) ((c : ℂ)+(t : ℂ)*I)) volume

/-- Paired Mellin inversion from absolute Dirichlet convergence and the
original analytic assumptions; no strip decay or axis identity is assumed. -/
theorem dirichlet_inversion_pair {a b : ℕ → ℂ} {d : ℕ → ℝ} {σ κ : ℝ}
    (hσ : 0 < σ) (hσκ : κ-σ < σ)
    (ha : Summable (fun n => ‖a n‖*Real.exp (-σ*d n)))
    (hb : Summable (fun n => ‖b n‖*Real.exp (-σ*d n)))
    {F G : ℂ → ℂ} (hhol : Differentiable ℂ F) (hfinite : Bound F)
    (hF : ∀ z : ℂ, z.re=σ → F z=Gamma z*series a d z)
    (hG : ∀ z : ℂ, z.re=σ → G z=Gamma z*series b d z)
    {ε : ℂ} (hε : ‖ε‖=1) (hFE : ∀ z, F z=ε*G ((κ : ℂ)-z)) (l : ℝ) :
    (∑' n, a n*(Real.exp (-Real.exp (l+d n)) : ℂ)) =
      ε*Complex.exp ((-l*κ : ℝ):ℂ)*(∑' n, b n*(Real.exp (-Real.exp (-l+d n)) : ℂ)) := by
  have he := contour_inversion_pair hhol hfinite hσκ
    (right_rapid hσ ha hF) (right_rapid hσ hb hG) hε hFE l
  have hi {a' : ℕ → ℂ} {F' : ℂ → ℂ}
      (ha' : Summable (fun n => ‖a' n‖*Real.exp (-σ*d n)))
      (hF' : ∀ z : ℂ, z.re=σ → F' z=Gamma z*series a' d z) (t : ℝ) :
      (1/(2*Real.pi):ℝ) • integral F' σ t =
        ∑' n, a' n*(Real.exp (-Real.exp (t+d n)) : ℂ) := by
    have hinv := FinitenessMellinSeries.inverse hσ ha' t
    rw [← mellinInv_congr_line hF', mellinInv_eq (Real.exp_pos t), Real.log_exp] at hinv
    exact hinv
  rw [← hi ha hF l, ← hi hb hG (-l), he,Complex.real_smul,Complex.real_smul]
  ring

open Filter Asymptotics FinitenessOriginalInput FinitenessInputBounds
  FinitenessCompletedNormalization FinitenessOriginalInversion
  FinitenessOriginalFourier FinitenessFourierConstruction FinitenessOriginalFricke

theorem normalize_pair_FE {F G : ℂ → ℂ} {ε : ℂ}
    (hFE : ∀ s : ℂ, F s=ε*G (1-s)) (c : ℂ) (b α : ℝ) (z : ℂ) :
    normalize F c b α z=ε*normalize G c b α (((1+2*α : ℝ):ℂ)-z) := by
  unfold FinitenessCompletedNormalization.normalize
  rw [hFE]
  have he : 1-(z-(α : ℂ))=(((1+2*α : ℝ):ℂ)-z)-(α : ℂ) := by push_cast; ring
  rw [he]
  ring

/-- The normalized coefficients and critical line remain exactly those
of the paper. The two sequences need not be equal or satisfy Euler products. -/
theorem original_inversion_pair {N : ℕ} (hN : 0 < N) (k : ℕ)
    {f g : ℕ → ℂ} {τ υ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (hg : g =O[atTop] (fun n : ℕ => (n : ℝ)^υ))
    (F G : ℂ → ℂ) (hhol : Differentiable ℂ F) (hfinite : FiniteOrder F)
    {c d : ℝ} (hc : ∀ s : ℂ, c<s.re → F s=completed N k f s)
    (hd : ∀ s : ℂ, d<s.re → G s=completed N k g s)
    {ε : ℂ} (hε : ‖ε‖=1) (hFE : ∀ s : ℂ, F s=ε*G (1-s)) :
    ∀ l : ℝ, laplace N k f l =
      ε*Complex.exp (((-l*(k : ℝ):ℝ):ℂ))*laplace N k g (-l) := by
  obtain ⟨σ,hσ⟩ := exists_gt
    (max (max 0 ((k : ℝ)/2))
      (max (max (τ+alpha k+1) (υ+alpha k+1)) (max (c+alpha k) (d+alpha k))))
  have hσ0 : 0 < σ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hσ
  have hσk : (k : ℝ)/2 < σ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hσ
  have hr := lt_of_le_of_lt (le_max_right _ _) hσ
  have hτ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hr
  have hυ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hr
  have hσc := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hr
  have hσd := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hr
  let F' := normalize F (constant N k) (exponent N) (alpha k)
  let G' := normalize G (constant N k) (exponent N) (alpha k)
  have hFhol : Differentiable ℂ F' := normalize_holomorphic hhol _ _ _
  have hFfinite : Bound F' :=
    normalize_finiteOrder (finiteOrder_bound hhol.continuous hfinite) _ _ _
  have hs {a : ℕ → ℂ} {A : ℂ → ℂ} {r : ℝ}
      (hA : ∀ s : ℂ, r<s.re → A s=completed N k a s) (hr : r+alpha k<σ) :
      ∀ z : ℂ, z.re=σ → normalize A (constant N k) (exponent N) (alpha k) z=
        Gamma z*series (normalizedCoefficients a k) (scaledFrequencies N) z := by
    intro z hz
    apply normalize_series (constant_ne_zero N k)
    rw [hA _ (by simp only [sub_re,ofReal_re,hz]; linarith),completed_exponential hN]
    simp only [sub_add_cancel]
  have halpha : 1+2*alpha k=(k : ℝ) := by unfold alpha; ring
  have hFE' : ∀ z : ℂ, F' z=ε*G' ((k : ℂ)-z) := by
    intro z
    simpa only [halpha,ofReal_natCast] using
      normalize_pair_FE hFE (constant N k) (exponent N) (alpha k) z
  intro l
  exact dirichlet_inversion_pair hσ0 (by linarith : (k : ℝ)-σ<σ)
    (normalized_absolute (N := N) hf hτ) (normalized_absolute (N := N) hg hυ)
    hFhol hFfinite (hs hc hσc) (hs hd hσd) hε hFE' l

/-- Paired completed functional equations give the literal two-series
Fricke law on the whole upper half-plane, with the specified multiplier. -/
theorem original_fricke_pair {N k : ℕ} (hN : 0 < N)
    {f g : ℕ → ℂ} (hf0 : f 0=0) (hg0 : g 0=0) {τ υ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (hg : g =O[atTop] (fun n : ℕ => (n : ℝ)^υ))
    (F G : ℂ → ℂ) (hhol : Differentiable ℂ F) (hfinite : FiniteOrder F)
    {c d : ℝ} (hc : ∀ s : ℂ, c<s.re → F s=completed N k f s)
    (hd : ∀ s : ℂ, d<s.re → G s=completed N k g s)
    {ε : ℂ} (hε : ‖ε‖=1) (hFE : ∀ s : ℂ, F s=ε*G (1-s)) :
    ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f k) z=
      (ε*I^k)/((((Real.sqrt N : ℝ):ℂ)*z)^k)*
        fourier (fullCoefficients g k) (-1/((N : ℂ)*z)) := by
  have hinv := original_inversion_pair hN k hf hg F G hhol hfinite hc hd hε hFE
  have he (l : ℝ) : fourier (fullCoefficients f k) ((height N l : ℂ)*I)=
      ε*Complex.exp (((-l*(k : ℝ):ℝ):ℂ))*
        fourier (fullCoefficients g k) ((height N (-l) : ℂ)*I) := by
    simpa only [laplace_eq_fourier hf0 hf,laplace_eq_fourier hg0 hg] using hinv l
  have hclear : ∀ z : ℂ, 0<z.im →
      (((Real.sqrt N : ℝ):ℂ)*z)^k*fourier (fullCoefficients f k) z=
        (ε*I^k)*fourier (fullCoefficients g k) (-1/((N : ℂ)*z)) := by
    apply FinitenessAxisIdentity.eq_of_axis
    · intro z hz
      exact (((differentiableAt_const _).mul differentiableAt_id).pow k).mul
        (holomorphic (polynomial_bound hf0 hf k) hz)
    · intro z hz
      exact (differentiableAt_const _).mul
        (FinitenessAxisIdentity.reflected_holomorphic
          (fun _ hz => holomorphic (polynomial_bound hg0 hg k) hz)
          (by exact_mod_cast hN) hz)
    · intro y hy
      obtain ⟨l,rfl⟩ := height_surjective (N := N) hy
      rw [height_reflected hN,he l]
      calc
        _ = ε*(((((Real.sqrt N : ℝ):ℂ)*((height N l : ℂ)*I))^k)*
            Complex.exp (((-l*(k : ℝ):ℝ):ℂ)))*
              fourier (fullCoefficients g k) ((height N (-l) : ℂ)*I) := by ring
        _ = _ := by rw [axis_multiplier hN]
  intro z hz
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : ((((Real.sqrt N : ℝ):ℂ)*z)^k) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hn).ne') hz0)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).mpr
  rw [mul_comm,hclear z hz]

#print axioms dirichlet_inversion_pair
#print axioms original_inversion_pair
#print axioms original_fricke_pair

end QuantitativeArithmeticPairedMellin
