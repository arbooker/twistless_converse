module

public import SmallLevelTaylorRowNormalizationV1
public import FinitenessOriginalTwistedContinuationsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct FinitenessFourierConstruction

/-- The paper's full Taylor--Fricke identity for every positive Ramanujan
modulus, every nonzero real translation, and every Taylor order. All analytic
bounds and the transformation law follow from the original Euler input.
The sign is chosen once, before q, and zero twists are included. -/
theorem original_ramanujan_taylor_rows {N k : ℕ} (hN : 0<N) (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ
          (mellin (frickeError k (fullCoefficients (twisted f q) k)
            (Nat.lcm N (q^2)) r (root N f q*ε*I^k) M))
          {s : ℂ | B-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          SmallLevelAdditive.transform (fullCoefficients (twisted f q) k) r s-
            (root N f q*ε*I^k)*(((Nat.lcm N (q^2):ℝ)*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*
              normalizedTaylorSum k (fullCoefficients (twisted f q) k) (Nat.lcm N (q^2)) r M s=
            mellin (frickeError k (fullCoefficients (twisted f q) k)
              (Nat.lcm N (q^2)) r (root N f q*ε*I^k) M) s := by
  obtain ⟨ε,hε,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨ε,hε,?_⟩
  intro q hq r hr
  have hL : 0<Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hq _)
  apply normalized_taylor_mellin_rows (by exact_mod_cast hL) hr k hk
    (polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) k)
    (fullCoefficients_zero (twisted_zero hf.zero q) k) (root N f q*ε*I^k)
  intro z hz
  have hreflect : 0<(-1/((Nat.lcm N (q^2):ℕ)*z)).im := by
    simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L := (Nat.lcm N (q^2):ℝ)) (by exact_mod_cast hL) hz
  simpa only [Complex.ofReal_natCast,fourier_twisted hf.zero hg q k hz,
    fourier_twisted hf.zero hg q k hreflect] using hlaw q hq z hz

#print axioms original_ramanujan_taylor_rows
end SmallLevelTaylor
