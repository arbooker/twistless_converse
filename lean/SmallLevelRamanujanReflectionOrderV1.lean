module

public import SmallLevelMellinUnscaleV1
public import SmallLevelTaylorTheoryV4
public import QuantitativeArithmeticCoherentTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelRamanujanReflectionOrder
open Complex MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct FinitenessFourierConstruction FinitenessAllLevelAxisDecay
open SmallLevelTaylor

/-- Finite order and reflection of every actual Ramanujan Mellin integral,
with the same original sign for all moduli. -/
theorem original_ramanujan_laws {N k : ℕ} (hN : 0<N) (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw N k f ε)
    {q : ℕ} (hq : 0<q) :
    FinitenessFiniteOrder.Bound (ramanujanEntire N k f q) ∧
    ∀ s : ℂ, ramanujanEntire N k f q s=
      (root N f q*ε)*(Real.sqrt (Nat.lcm N (q^2)):ℂ)^((k:ℂ)-2*s)*
        ramanujanEntire N k f q ((k:ℂ)-s) := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have ha := polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) k
  have ha0 := fullCoefficients_zero (twisted_zero hf.zero q) k
  have hL : 0<Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hq _)
  have hroot : root N f q*ε≠0 := by
    rcases root_unit hf.toEulerData q with h|h <;> rcases hε with he|he <;> simp [h,he]
  have hfr : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients (twisted f q) k) z=
      ((root N f q*ε)*I^k)/(((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^k)*
        fourier (fullCoefficients (twisted f q) k) (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
    intro z hz
    have hreflect : 0<(-1/((Nat.lcm N (q^2):ℂ)*z)).im := by
      simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
        (L := (Nat.lcm N (q^2):ℝ)) (by exact_mod_cast hL) hz
    simpa only [fourier_twisted hf.zero hg q k hz,fourier_twisted hf.zero hg q k hreflect] using hlaw q hq z hz
  have hm := FinitenessAllLevelMellinPair.mellin_entire hL hk _ ha ha0 (root N f q*ε) hroot hfr
  have he : ramanujanEntire N k f q=mellin (axis 1 (fullCoefficients (twisted f q) k)) := by
    have haxis : axis 1 (fullCoefficients (twisted f q) k)=
        (fun y : ℝ => fourier (fullCoefficients (twisted f q) k) ((y:ℂ)*I)) := by
      funext y
      simp [axis]
    rw [haxis]
    rfl
  rw [he]
  exact ⟨SmallLevelMellinUnscale.finite_order_at_one hL _ hm.2.1,
    SmallLevelMellinUnscale.reflection_pair hL _ _ (root N f q*ε) hm.2.2⟩

#print axioms original_ramanujan_laws
end SmallLevelRamanujanReflectionOrder
