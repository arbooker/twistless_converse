module

public import FinitenessAllLevelMellinPairV1
public import QuantitativeArithmeticMellinScaleV1
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelNineteenTwoMellin. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelNineteenGridTwoMellinV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenTwoMellin
open Complex Filter Asymptotics Set MeasureTheory FinitenessPolynomialSeries
  FinitenessFourierConstruction FinitenessAllLevelAxisDecay FinitenessAllLevelMellinPair

/-- The same rapid-decay argument as the existing self-pair construction,
now for two distinct Fourier series related by an actual matrix law. -/
theorem two_axis_relation {N k : ℕ} (hN : 0 < N) (a b : ℕ → ℂ) (ε : ℂ)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier a z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier b (-1 / ((N : ℂ) * z))) {t : ℝ} (ht : 0 < t) :
    axis N a t = ε / (t : ℂ) ^ k * axis N b (1 / t) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have h := hfr (((t / Real.sqrt N : ℝ) : ℂ) * I)
    (by simpa only [mul_I_im, ofReal_re] using div_pos ht hs)
  simpa only [axis, reflected_scaled hN ht, scaled_multiplier hN k ε ht] using h

def two_pair {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (a b : ℕ → ℂ)
    (ha : PolynomialBound a) (ha0 : a 0 = 0)
    (hb : PolynomialBound b) (hb0 : b 0 = 0) (ε : ℂ) (hε : ε ≠ 0)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier a z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier b (-1 / ((N : ℂ) * z))) : WeakFEPair ℂ where
  f := axis N a
  g := axis N b
  k := k
  ε := ε
  f₀ := 0
  g₀ := 0
  hf_int := (axis_continuous hN ha).locallyIntegrableOn measurableSet_Ioi
  hg_int := (axis_continuous hN hb).locallyIntegrableOn measurableSet_Ioi
  hk := by exact_mod_cast hk
  hε := hε
  h_feq := by
    intro t ht
    have h := two_axis_relation hN a b ε hfr (one_div_pos.mpr ht)
    simpa only [one_div_one_div, ofReal_div, ofReal_one, one_div, ofReal_inv, inv_pow, one_mul,
      div_inv_eq_mul, Real.rpow_natCast, ofReal_pow, smul_eq_mul] using h
  hf_top := by intro r; simpa only [sub_zero] using axis_rapid hN ha ha0 r
  hg_top := by intro r; simpa only [sub_zero] using axis_rapid hN hb hb0 r

theorem two_pair_strong {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (a b : ℕ → ℂ)
    (ha : PolynomialBound a) (ha0 : a 0 = 0)
    (hb : PolynomialBound b) (hb0 : b 0 = 0) (ε : ℂ) (hε : ε ≠ 0)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier a z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier b (-1 / ((N : ℂ) * z))) :
    IsStrongFEPair (two_pair hN hk a b ha ha0 hb hb0 ε hε hfr) := ⟨rfl, rfl⟩

/-- The actual scaled Fourier Mellin transform is entire of finite order.
Its reflected equation retains the same original root number. -/
theorem two_mellin_entire {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (a b : ℕ → ℂ)
    (ha : PolynomialBound a) (ha0 : a 0 = 0)
    (hb : PolynomialBound b) (hb0 : b 0 = 0) (ε : ℂ) (hε : ε ≠ 0)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier a z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier b (-1 / ((N : ℂ) * z))) :
    Differentiable ℂ (mellin (axis N a)) ∧
      FinitenessFiniteOrder.Bound (mellin (axis N a)) ∧
      ∀ w : ℂ, mellin (axis N a) w = ε * mellin (axis N b) ((k : ℂ) - w) := by
  let P := two_pair hN hk a b ha ha0 hb hb0 ε hε hfr
  have hP : IsStrongFEPair P := two_pair_strong hN hk a b ha ha0 hb hb0 ε hε hfr
  have he : P.Λ = mellin (axis N a) := funext (fun w => (hP.hasMellin w).2.symm)
  have he' : P.symm.Λ = mellin (axis N b) := funext (fun w => (hP.symm.hasMellin w).2.symm)
  obtain ⟨Ca, ca, hCa, hca, hba⟩ := axis_exponential hN ha ha0
  obtain ⟨Cb, cb, hCb, hcb, hbb⟩ := axis_exponential hN hb hb0
  refine ⟨he ▸ hP.differentiable_Λ,
    he ▸ AsymptoticClassicalLSeries.strongPair_finiteOrder P hP hCa hCb hca hcb hba hbb, ?_⟩
  intro w
  have h := P.functional_equation ((k : ℂ) - w)
  rw [he, he'] at h
  simpa only [P, two_pair, ofReal_natCast, sub_sub_cancel, smul_eq_mul] using h

#print axioms two_axis_relation
#print axioms two_pair_strong
#print axioms two_mellin_entire
end QuantitativeArithmeticSmallLevelNineteenTwoMellin
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenGridCenterEntireV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenTwoMellin
open Complex Set MeasureTheory SmallLevelAdditive SmallLevelTaylor
open FinitenessPolynomialSeries FinitenessFourierConstruction FinitenessAllLevelAxisDecay

/-- An actual invariant matrix supplies an entire continuation at the cusp
sent to infinity. The two Fourier translates need not be equal. -/
theorem matrix_center_entire {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) (hk : 0<k) (A B C D : ℝ) (hC : C≠0)
    (hdet : A*D-B*C=1) (N : ℕ) (hN : 0<N) (hC2 : C^2=(N:ℝ))
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      1/(((C:ℂ)*z+(D:ℂ))^k)*fourier a (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ)))) :
    (∀ s : ℂ, AnalyticAt ℂ
      (mellin (fun t : ℝ => fourier a (((-D/C:ℝ):ℂ)+(t:ℂ)*I))) s) ∧
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      mellin (fun t : ℝ => fourier a (((-D/C:ℝ):ℂ)+(t:ℂ)*I)) s=
        transform a (-D/C) s := by
  have hs : (Real.sqrt (N:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (show (0:ℝ)<N by exact_mod_cast hN)).ne'
  have hc : (C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hC
  let ε : ℂ := ((Real.sqrt (N:ℝ):ℂ)/(C:ℂ))^k/I^k
  have hε : ε≠0 := div_ne_zero (pow_ne_zero _ (div_ne_zero hs hc))
    (pow_ne_zero _ I_ne_zero)
  have htwo := QuantitativeArithmeticTwoSequenceTaylor.matrix_two_series a k A B C D
    hC (by rw [hdet]; norm_num) 1 hF
  dsimp only at htwo
  simp only [hdet,div_one,hC2,one_mul] at htwo
  have hm := (two_mellin_entire hN hk (coefficients a (-D/C)) (coefficients a (A/C))
    (coefficients_polynomial ha _) (coefficients_zero ha0 _)
    (coefficients_polynomial ha _) (coefficients_zero ha0 _) ε hε
    (by simpa only [Complex.ofReal_natCast,ε,div_mul_cancel₀ _ (pow_ne_zero k I_ne_zero)] using htwo)).1
  have hm1 := QuantitativeArithmeticMellinScale.entire_at_one hN _ hm
  have he : axis 1 (coefficients a (-D/C))=
      (fun t : ℝ => fourier a (((-D/C:ℝ):ℂ)+(t:ℂ)*I)) :=
    funext (axis_one_translate a (-D/C))
  rw [he] at hm1
  refine ⟨fun s => hm1.analyticAt s,?_⟩
  obtain ⟨bound,hbound⟩ := additive_convergence_halfplane ha ha0
  exact ⟨bound,fun s hs => (hbound (-D/C) s hs).2⟩

#print axioms matrix_center_entire
end QuantitativeArithmeticSmallLevelNineteenTwoMellin
end
end
