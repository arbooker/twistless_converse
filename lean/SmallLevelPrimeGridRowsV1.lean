module
public import SmallLevelRamifiedPrimeAdditiveV1
public import SmallLevelTaylorTheoryV4
public import SmallLevelFourPrimeRatesV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelPrimeGrid
open Complex SmallLevelAdditive SmallLevelPrimeRates SmallLevelTaylor

theorem reflected_parameter (p m : ℕ) (s : ℂ) :
    (p:ℂ)^((m:ℂ)-s)=(parameter p m s)⁻¹ := by
  rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
  rfl

theorem ramified_parameter (m : ℕ) (f : ℕ→ℂ) {p : ℕ} (hp : p≠0) (s : ℂ) :
    SmallLevelRamifiedPrimeAdditive.heckeScalar m f p s=
      ((Real.sqrt p:ℂ)*f p)*(parameter p m s)⁻¹ := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp
  have hc : (p:ℂ)^((m:ℂ)-s)=(p:ℂ)^m*(p:ℂ)^(-s) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ hp0,Complex.cpow_natCast]
  rw [←reflected_parameter,hc]
  unfold SmallLevelRamifiedPrimeAdditive.heckeScalar
    QuantitativeArithmeticRamifiedFullTrace.multiplier
  ring

/-- Good-prime grid equations, retaining zero auxiliary eigenvalues. -/
theorem original_good_rows {N m p Q : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f)
    (hp : p.Prime) (hgood : ¬p∣N) (hQ : 0<Q) (hpQ : p∣Q) :
    ∃ B : ℝ, ∀ t : ℤ, ∀ s : ℂ, B<s.re →
      (∑ j∈Finset.range p,grid (2*m) f Q (t+(j:ℤ)*(Q/p:ℕ)) s)-
        ((Real.sqrt p:ℂ)*f p)*(parameter p m s)⁻¹*grid (2*m) f Q ((p:ℤ)*t) s+
        ((parameter p m s)⁻¹)^2*grid (2*m) f Q ((p:ℤ)^2*t) s=0 := by
  obtain ⟨B,hB⟩:=normalized_additive_hecke hf hp hgood
  refine ⟨B,?_⟩
  intro t s hs
  have hh:=hB ((t:ℝ)/Q) s hs
  simp_rw [grid_translation hQ hp.pos hpQ] at hh
  have h1 : (p:ℝ)*((t:ℝ)/Q)=(((p:ℤ)*t:ℤ):ℝ)/Q := by push_cast; ring
  have h2 : (p:ℝ)^2*((t:ℝ)/Q)=(((p:ℤ)^2*t:ℤ):ℝ)/Q := by push_cast; ring
  rw [h1,h2,reflected_parameter] at hh
  exact hh

/-- Ramified-prime grid equations from the original Euler coefficient law. -/
theorem original_ramified_rows {N m p Q : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f) (hm : 0<m)
    (hp : p.Prime) (hbad : p∣N) (hQ : 0<Q) (hpQ : p∣Q) :
    ∃ B : ℝ, ∀ t : ℤ, ∀ s : ℂ, B<s.re →
      (∑ j∈Finset.range p,grid (2*m) f Q (t+(j:ℤ)*(Q/p:ℕ)) s)-
        ((Real.sqrt p:ℂ)*f p)*(parameter p m s)⁻¹*grid (2*m) f Q ((p:ℤ)*t) s=0 := by
  obtain ⟨B,hB⟩:=SmallLevelRamifiedPrimeAdditive.original_ramified_row hp hbad m hm hf
  refine ⟨B,?_⟩
  intro t s hs
  have hh:=hB ((t:ℝ)/Q) s hs
  simp_rw [grid_translation hQ hp.pos hpQ] at hh
  have h1 : (p:ℝ)*((t:ℝ)/Q)=(((p:ℤ)*t:ℤ):ℝ)/Q := by push_cast; ring
  rw [h1,ramified_parameter m f hp.ne_zero] at hh
  exact sub_eq_zero.mpr hh

#print axioms original_good_rows
#print axioms original_ramified_rows
end SmallLevelPrimeGrid
