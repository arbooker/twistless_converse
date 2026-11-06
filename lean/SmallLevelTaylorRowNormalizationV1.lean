module

public import SmallLevelTaylorMellinRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessPolynomialSeries FinitenessFourierConstruction

theorem even_fricke_denominator {L r : ℝ} (hL : 0<L) (k : ℕ) (hk : Even k) :
    (((Real.sqrt L:ℂ)*(r:ℂ))^k)=((L*r^2:ℝ):ℂ)^(k/2) := by
  obtain ⟨m,rfl⟩ := hk
  have hs : (Real.sqrt L:ℂ)^2=(L:ℂ) := by exact_mod_cast Real.sq_sqrt hL.le
  have he : m+m=2*m := by omega
  rw [he,Nat.mul_div_cancel_left m (by decide : 0<2),pow_mul,mul_pow,hs]
  push_cast
  rfl

theorem normalized_taylor_scalar {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) (hk : Even k) (χ s : ℂ) (n : ℕ) :
    (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
      ((I/(r:ℂ))^n*((L*r^2:ℝ):ℂ)^(s+(n:ℂ)))=
        χ*((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*(I*(L:ℂ)*(r:ℂ))^n := by
  have hc : 0<L*r^2 := mul_pos hL (sq_pos_of_ne_zero hr)
  have hc0 : ((L*r^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  have hkdiv : ((k/2:ℕ):ℂ)=(k:ℂ)/2 := by
    obtain ⟨m,rfl⟩ := hk
    rw [show m+m=2*m by omega,Nat.mul_div_cancel_left m (by decide : 0<2)]
    push_cast
    ring
  rw [even_fricke_denominator hL k hk,Complex.cpow_add _ _ hc0,
    Complex.cpow_natCast,← hkdiv,Complex.cpow_sub _ _ hc0,Complex.cpow_natCast]
  have hn : (I/(r:ℂ))^n*((L*r^2:ℝ):ℂ)^n=(I*(L:ℂ)*(r:ℂ))^n := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp
  calc
    _=(χ/((L*r^2:ℝ):ℂ)^(k/2))*((L*r^2:ℝ):ℂ)^s*
        ((I/(r:ℂ))^n*((L*r^2:ℝ):ℂ)^n) := by ring
    _=_ := by rw [hn]; ring

def normalizedTaylorSum (k : ℕ) (a : ℕ → ℂ) (L r : ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ n∈Finset.range M, (I*(L:ℂ)*(r:ℂ))^n*Ring.choose (s+(n:ℂ)-(k:ℂ)) n*
    SmallLevelAdditive.transform a (-1/(L*r)) (s+(n:ℂ))

theorem normalized_taylor_sum {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) (hk : Even k) (a : ℕ → ℂ) (χ s : ℂ) (M : ℕ) :
    (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
      (∑ n∈Finset.range M, mellinTaylorTerm k a (-1/(L*r)) (L*r^2) r n s)=
      χ*((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*normalizedTaylorSum k a L r M s := by
  unfold normalizedTaylorSum
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  unfold mellinTaylorTerm
  calc
    _=((χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
        ((I/(r:ℂ))^n*((L*r^2:ℝ):ℂ)^(s+(n:ℂ))))*
        Ring.choose (s+(n:ℂ)-(k:ℂ)) n*SmallLevelAdditive.transform a (-1/(L*r)) (s+(n:ℂ)) := by ring
    _=_ := by rw [normalized_taylor_scalar hL hr k hk χ s n]; ring

theorem normalized_taylor_mellin_rows {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) (hk : Even k) {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier a (-1/((L:ℂ)*z))) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError k a L r χ M)) {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        SmallLevelAdditive.transform a r s-
          χ*((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*normalizedTaylorSum k a L r M s=
          mellin (frickeError k a L r χ M) s := by
  obtain ⟨B,hB⟩ := all_taylor_mellin_rows hL hr k ha ha0 χ hF
  refine ⟨B,fun M => ⟨(hB M).1,?_⟩⟩
  intro s hs
  rw [← normalized_taylor_sum hL hr k hk a χ s M]
  exact (hB M).2 s hs

#print axioms normalized_taylor_scalar
#print axioms normalized_taylor_mellin_rows
end SmallLevelTaylor
