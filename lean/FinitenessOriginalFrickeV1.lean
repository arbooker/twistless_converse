module

public import FinitenessAxisIdentityV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessOriginalFricke

open Complex FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction

theorem sqrt_height {N : ℕ} (hN : 0 < N) (l : ℝ) :
    Real.sqrt N*height N l=Real.exp l := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ)=Real.exp (Real.log N/2) := by
    rw [Real.exp_half, Real.exp_log hn]
  rw [hs, height, ← Real.exp_add]
  congr 1
  ring

theorem height_pair {N : ℕ} (hN : 0 < N) (l : ℝ) :
    (N : ℝ)*height N l*height N (-l)=1 := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold height
  rw [mul_assoc, ← Real.exp_add,
    show (l-Real.log N/2)+(-l-Real.log N/2) = -Real.log N by ring,
    Real.exp_neg, Real.exp_log hn, mul_inv_cancel₀ hn.ne']

theorem height_surjective {N : ℕ} {y : ℝ} (hy : 0 < y) : ∃ l : ℝ, height N l=y := by
  refine ⟨Real.log y+Real.log N/2, ?_⟩
  rw [height, add_sub_cancel_right, Real.exp_log hy]

theorem height_reflected {N : ℕ} (hN : 0 < N) (l : ℝ) :
    -1/((N : ℂ)*((height N l : ℂ)*I))=(height N (-l) : ℂ)*I := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hh : (height N l : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  apply (div_eq_iff (mul_ne_zero hn (mul_ne_zero hh I_ne_zero))).mpr
  have hp : (N : ℂ)*(height N l : ℂ)*(height N (-l) : ℂ)=1 := by
    exact_mod_cast height_pair hN l
  calc
    (-1 : ℂ) = (1 : ℂ)*(I*I) := by rw [I_mul_I, one_mul]
    _ = ((N : ℂ)*(height N l : ℂ)*(height N (-l) : ℂ))*(I*I) := by rw [hp]
    _ = _ := by ring

theorem axis_multiplier {N : ℕ} (hN : 0 < N) (k : ℕ) (l : ℝ) :
    (((Real.sqrt N : ℝ):ℂ)*((height N l : ℂ)*I))^k*
      Complex.exp (((-l*(k : ℝ):ℝ):ℂ))=I^k := by
  have hh : (((Real.sqrt N : ℝ):ℂ)*((height N l : ℂ)*I))=(Real.exp l : ℂ)*I := by
    rw [← mul_assoc, ← ofReal_mul, sqrt_height hN]
  rw [hh, mul_pow, ofReal_exp, ← Complex.exp_nat_mul]
  calc
    _ = (Complex.exp ((k : ℂ)*(l : ℂ))*Complex.exp (((-l*(k : ℝ):ℝ):ℂ)))*I^k := by ring
    _ = I^k := by
      rw [← Complex.exp_add]
      have he : (k : ℂ)*(l : ℂ)+(((-l*(k : ℝ):ℝ):ℂ))=0 := by push_cast; ring
      rw [he, Complex.exp_zero, one_mul]

/-- An axis inversion law gives the full Fricke law with the same scalar. -/
theorem fricke_of_inversion {N k : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf0 : f 0=0) {τ : ℝ} (hg : f =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^τ))
    (ε : ℂ) (heL : ∀ l : ℝ, FinitenessOriginalInversion.laplace N k f l=
      ε*Complex.exp (((-l*(k:ℝ):ℝ):ℂ))*FinitenessOriginalInversion.laplace N k f (-l)) :
    ∀ z : ℂ, 0 < z.im →
      fourier (fullCoefficients f k) z =
        ((ε : ℂ)*I^k)/((((Real.sqrt N : ℝ):ℂ)*z)^k)*fourier (fullCoefficients f k) (-1/((N : ℂ)*z)) := by
  have he (l : ℝ) : fourier (fullCoefficients f k) ((height N l : ℂ)*I) =
      (ε : ℂ)*Complex.exp (((-l*(k : ℝ) : ℝ):ℂ))*fourier (fullCoefficients f k) ((height N (-l) : ℂ)*I) := by
    simpa only [FinitenessOriginalFourier.laplace_eq_fourier hf0 hg] using heL l
  let χ : ℂ := (ε : ℂ)*I^k
  have hhol : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ (fourier (fullCoefficients f k)) z :=
    fun _ hz => holomorphic (polynomial_bound hf0 hg k) hz
  have hclear : ∀ z : ℂ, 0 < z.im →
      (((Real.sqrt N : ℝ):ℂ)*z)^k*fourier (fullCoefficients f k) z =
      χ*fourier (fullCoefficients f k) (-1/((N : ℂ)*z)) := by
    apply FinitenessAxisIdentity.fricke_of_axis hhol (by exact_mod_cast hN) k χ
    intro y hy
    obtain ⟨l,rfl⟩ := height_surjective (N := N) hy
    simp only [ofReal_natCast]
    rw [height_reflected hN, he l]
    calc
      _ = (ε : ℂ)*
          (((((Real.sqrt N : ℝ):ℂ)*((height N l : ℂ)*I))^k)*Complex.exp (((-l*(k : ℝ):ℝ):ℂ)))*
          fourier (fullCoefficients f k) ((height N (-l) : ℂ)*I) := by ring
      _ = _ := by rw [axis_multiplier hN]
  intro z hz
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd : ((((Real.sqrt N : ℝ):ℂ)*z)^k) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hn).ne') hz0)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hd).mpr
  rw [mul_comm, hclear z hz]

/-- The full holomorphic transformation preserves a specified completion
root number; it does not choose a new sign for each twist. -/
theorem fricke_with_sign {N k : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (hf0 : f 0=0) {τ : ℝ} (hg : f =O[Filter.atTop] (fun n : ℕ => (n:ℝ)^τ))
    (F : ℂ → ℂ) (hhol : Differentiable ℂ F) (hfinite : FiniteOrder F)
    {c : ℝ} (hc : ∀ s : ℂ, c<s.re → F s=completed N k f s)
    {ε : ℂ} (hεnorm : ‖ε‖=1) (hFE : ∀ s : ℂ, F s=ε*F (1-s)) :
    ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f k) z=
      (ε*I^k)/((((Real.sqrt N:ℝ):ℂ)*z)^k)*
        fourier (fullCoefficients f k) (-1/((N:ℂ)*z)) :=
  fricke_of_inversion hN hf0 hg ε
    (FinitenessOriginalInversion.inversion_with_sign hN k hg F hhol hfinite hc hεnorm hFE)

/-- Original solution hypotheses imply the literal holomorphic Fricke law
on the FULL upper half-plane, with a unit scalar and the exact conductor. -/
theorem fricke_of_continuation {N k : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf0 : f 0=0) {τ : ℝ} (hg : f =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^τ))
    (hcont : Continuation N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε = -1) ∧ ∀ z : ℂ, 0 < z.im →
      fourier (fullCoefficients f k) z =
        ((ε : ℂ)*I^k)/((((Real.sqrt N : ℝ):ℂ)*z)^k)*fourier (fullCoefficients f k) (-1/((N : ℂ)*z)) := by
  obtain ⟨ε,hε,heL⟩ := FinitenessOriginalInversion.inversion hN k hg hcont
  exact ⟨ε,hε,fricke_of_inversion hN hf0 hg ε heL⟩

theorem solution_fricke {N k : ℕ} (hN : 0 < N) {f : ℕ → ℂ} (hf : IsSolution N k f) :
    ∃ χ : ℂ, ‖χ‖=1 ∧ ∀ z : ℂ, 0 < z.im →
      fourier (fullCoefficients f k) z =
        χ/((((Real.sqrt N : ℝ):ℂ)*z)^k)*fourier (fullCoefficients f k) (-1/((N : ℂ)*z)) := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  obtain ⟨ε,hε,he⟩ := fricke_of_continuation hN hf.zero hg hf.continuation
  refine ⟨(ε : ℂ)*I^k,?_,he⟩
  rcases hε with h | h <;> simp [h]

#print axioms height_reflected
#print axioms axis_multiplier
#print axioms fricke_with_sign
#print axioms solution_fricke
#print axioms fricke_of_continuation

end FinitenessOriginalFricke
