module

public import FinitenessAllLevelAxisDecayV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelMellinPair

open Complex Filter Asymptotics Set MeasureTheory FinitenessPolynomialSeries
  FinitenessFourierConstruction FinitenessAllLevelAxisDecay

theorem reflected_scaled {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    -1 / ((N : ℂ) * (((t / Real.sqrt N : ℝ) : ℂ) * I)) =
      ((((1 / t) / Real.sqrt N : ℝ) : ℂ) * I) := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hsC : (Real.sqrt N : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hsq : (Real.sqrt N : ℂ) ^ 2 = (N : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N)
  push_cast
  rw [← hsq]
  field_simp
  simp [I_sq]

theorem scaled_multiplier {N : ℕ} (hN : 0 < N) (k : ℕ) (ε : ℂ) {t : ℝ} (ht : 0 < t) :
    (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * (((t / Real.sqrt N : ℝ) : ℂ) * I)) ^ k =
      ε / (t : ℂ) ^ k := by
  have hsC : (Real.sqrt N : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have he : (((Real.sqrt N : ℝ) : ℂ) * (((t / Real.sqrt N : ℝ) : ℂ) * I)) = (t : ℂ) * I := by
    push_cast
    field_simp
  rw [he, mul_pow]
  field_simp

theorem axis_relation {N k : ℕ} (hN : 0 < N) (a : ℕ → ℂ) (ε : ℂ)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier a z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier a (-1 / ((N : ℂ) * z))) {t : ℝ} (ht : 0 < t) :
    axis N a t = ε / (t : ℂ) ^ k * axis N a (1 / t) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have h := hfr (((t / Real.sqrt N : ℝ) : ℂ) * I)
    (by simpa only [mul_I_im, ofReal_re] using div_pos ht hs)
  simpa only [axis, reflected_scaled hN ht, scaled_multiplier hN k ε ht] using h

def pair {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (a : ℕ → ℂ)
    (ha : PolynomialBound a) (ha0 : a 0 = 0) (ε : ℂ) (hε : ε ≠ 0)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier a z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier a (-1 / ((N : ℂ) * z))) : WeakFEPair ℂ where
  f := axis N a
  g := axis N a
  k := k
  ε := ε
  f₀ := 0
  g₀ := 0
  hf_int := (axis_continuous hN ha).locallyIntegrableOn measurableSet_Ioi
  hg_int := (axis_continuous hN ha).locallyIntegrableOn measurableSet_Ioi
  hk := by exact_mod_cast hk
  hε := hε
  h_feq := by
    intro t ht
    have h := axis_relation hN a ε hfr (one_div_pos.mpr ht)
    simpa only [one_div_one_div, ofReal_div, ofReal_one, one_div, ofReal_inv, inv_pow, one_mul,
      div_inv_eq_mul, Real.rpow_natCast, ofReal_pow, smul_eq_mul] using h
  hf_top := by intro r; simpa only [sub_zero] using axis_rapid hN ha ha0 r
  hg_top := by intro r; simpa only [sub_zero] using axis_rapid hN ha ha0 r

theorem pair_strong {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (a : ℕ → ℂ)
    (ha : PolynomialBound a) (ha0 : a 0 = 0) (ε : ℂ) (hε : ε ≠ 0)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier a z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier a (-1 / ((N : ℂ) * z))) :
    IsStrongFEPair (pair hN hk a ha ha0 ε hε hfr) := ⟨rfl, rfl⟩

/-- The actual scaled Fourier Mellin transform is entire of finite order.
Its reflected equation retains the same original root number. -/
theorem mellin_entire {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (a : ℕ → ℂ)
    (ha : PolynomialBound a) (ha0 : a 0 = 0) (ε : ℂ) (hε : ε ≠ 0)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier a z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier a (-1 / ((N : ℂ) * z))) :
    Differentiable ℂ (mellin (axis N a)) ∧
      FinitenessFiniteOrder.Bound (mellin (axis N a)) ∧
      ∀ w : ℂ, mellin (axis N a) w = ε * mellin (axis N a) ((k : ℂ) - w) := by
  let P := pair hN hk a ha ha0 ε hε hfr
  have hP : IsStrongFEPair P := pair_strong hN hk a ha ha0 ε hε hfr
  have he : P.Λ = mellin (axis N a) := funext (fun w => (hP.hasMellin w).2.symm)
  have he' : P.symm.Λ = mellin (axis N a) := funext (fun w => (hP.symm.hasMellin w).2.symm)
  obtain ⟨C, c, hC, hc, hb⟩ := axis_exponential hN ha ha0
  refine ⟨he ▸ hP.differentiable_Λ,
    he ▸ AsymptoticClassicalLSeries.strongPair_finiteOrder P hP hC hC hc hc hb hb, ?_⟩
  intro w
  have h := P.functional_equation ((k : ℂ) - w)
  rw [he, he'] at h
  simpa only [P, pair, ofReal_natCast, sub_sub_cancel, smul_eq_mul] using h

#print axioms axis_relation
#print axioms pair_strong
#print axioms mellin_entire

end FinitenessAllLevelMellinPair
