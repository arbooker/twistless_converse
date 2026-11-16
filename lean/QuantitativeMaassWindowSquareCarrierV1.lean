module

public import QuantitativeMaassCarrierConvolutionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

def windowSquareCarrierPlus (K : SchwartzMap ℝ ℝ) (R ε t : ℝ) : ℝ → ℂ :=
  carrierSquareAmplitude (windowCarrier (kernelTimeProfile K) R ε)
    (fun s => windowCarrier (kernelTimeProfile K) R ε (-s)) (-2*t)

def windowSquareCarrierMinus (K : SchwartzMap ℝ ℝ) (R ε t : ℝ) : ℝ → ℂ :=
  carrierSquareAmplitude (fun s => windowCarrier (kernelTimeProfile K) R ε (-s))
    (windowCarrier (kernelTimeProfile K) R ε) (2*t)

/-- Both actual square amplitudes are smooth and compactly supported. -/
theorem windowSquareCarrier_regular (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R ε t : ℝ) (hR : 0<R) :
    ContDiff ℝ ∞ (windowSquareCarrierPlus K R ε t) ∧
    HasCompactSupport (windowSquareCarrierPlus K R ε t) ∧
    ContDiff ℝ ∞ (windowSquareCarrierMinus K R ε t) ∧
    HasCompactSupport (windowSquareCarrierMinus K R ε t) := by
  let a := windowCarrier (kernelTimeProfile K) R ε
  have ha : ContDiff ℝ ∞ a := windowCarrier_smooth _ (kernelTimeProfile_smooth K) R ε
  have hac : HasCompactSupport a := windowCarrier_compact _ (kernelTimeProfile_compact K hc) R ε hR
  have hb : ContDiff ℝ ∞ (fun u => a (-u)) := by fun_prop
  have hbc : HasCompactSupport (fun u => a (-u)) := hac.comp_homeomorph (Homeomorph.neg ℝ)
  exact ⟨carrierSquareAmplitude_smooth a _ _ ha hac hb,
    carrierSquareAmplitude_compact a _ _ hac hbc,
    carrierSquareAmplitude_smooth _ a _ hb hbc ha,
    carrierSquareAmplitude_compact _ a _ hbc hac⟩

/-- Exact two-frequency decomposition of the ORIGINAL Schwartz time square. -/
theorem windowTimeSquare_carriers (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R ε t : ℝ) (hR : 0<R) (hε : 0≤ε) :
    (timeConvolution (windowTimeSchwartz K hc R hR (t-ε) (t+ε))
      (windowTimeSchwartz K hc R hR (t-ε) (t+ε)) : ℝ → ℂ)=
      timeFrequencyShift t (windowSquareCarrierPlus K R ε t)+
      timeFrequencyShift (-t) (windowSquareCarrierMinus K R ε t) := by
  let a := windowCarrier (kernelTimeProfile K) R ε
  have ha : ContDiff ℝ ∞ a := windowCarrier_smooth _ (kernelTimeProfile_smooth K) R ε
  have hac : HasCompactSupport a := windowCarrier_compact _ (kernelTimeProfile_compact K hc) R ε hR
  have hb : ContDiff ℝ ∞ (fun u => a (-u)) := by fun_prop
  have hbc : HasCompactSupport (fun u => a (-u)) := hac.comp_homeomorph (Homeomorph.neg ℝ)
  have hfun : symmetricWindowTimeTest K R (t-ε) (t+ε)=
      timeFrequencyShift t a+timeFrequencyShift (-t) (fun u => a (-u)) := by
    funext s
    exact symmetricWindowTimeTest_carriers K he R t ε s hε
  rw [timeConvolution_eq_function]
  change timeFunctionConvolution (symmetricWindowTimeTest K R (t-ε) (t+ε))
    (symmetricWindowTimeTest K R (t-ε) (t+ε))=_
  rw [hfun]
  exact timeFunctionConvolution_pair_square a (fun u => a (-u)) t ha hac hb hbc

/-- Actual convolution-square carrier estimates with constants chosen before
R, epsilon and the spectral center. No derivatives of the rapidly oscillating
second convolution factor are taken. -/
theorem windowSquareCarrier_uniform_bounds (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (m : ℕ) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ R : ℝ,1≤R → ∀ ε : ℝ,0≤ε → ε≤1 → ∀ t : ℝ,
      Function.support (windowSquareCarrierPlus K R ε t)⊆Icc (-(2*(B*R))) (2*(B*R)) ∧
      Function.support (windowSquareCarrierMinus K R ε t)⊆Icc (-(2*(B*R))) (2*(B*R)) ∧
      ∀ n : ℕ,n≤m → ∀ s : ℝ,
        ‖iteratedDeriv n (windowSquareCarrierPlus K R ε t) s‖≤C*R*ε^2 ∧
        ‖iteratedDeriv n (windowSquareCarrierMinus K R ε t) s‖≤C*R*ε^2 := by
  obtain ⟨B,C,hB,hC,hbound⟩ := kernel_windowCarrier_uniform_bounds K hc m
  refine ⟨B,4*B*C^2,hB,by positivity,?_⟩
  intro R hR ε hε hε1 t
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  obtain ⟨hs,hd⟩ := hbound R hR ε hε hε1
  let a := windowCarrier (kernelTimeProfile K) R ε
  let b : ℝ → ℂ := fun u => a (-u)
  have ha : ContDiff ℝ ∞ a := windowCarrier_smooth _ (kernelTimeProfile_smooth K) R ε
  have hac : HasCompactSupport a := windowCarrier_compact _ (kernelTimeProfile_compact K hc) R ε hRp
  have hb : ContDiff ℝ ∞ b := by dsimp only [b];fun_prop
  have hbc : HasCompactSupport b := hac.comp_homeomorph (Homeomorph.neg ℝ)
  have hsa : Function.support a⊆Icc (-(B*R)) (B*R) := hs
  have hsb : Function.support b⊆Icc (-(B*R)) (B*R) := by
    intro u hu
    have hh := hsa hu
    constructor <;> linarith [hh.1,hh.2]
  refine ⟨carrierSquareAmplitude_support a b _ (B*R) hsa hsb,
    carrierSquareAmplitude_support b a _ (B*R) hsb hsa,?_⟩
  intro n hn s
  have ha0 (u : ℝ) : ‖a u‖≤C*ε := by
    simpa only [iteratedDeriv_zero] using (hd 0 (Nat.zero_le m) u).1
  have hb0 (u : ℝ) : ‖b u‖≤C*ε := by
    simpa only [iteratedDeriv_zero] using (hd 0 (Nat.zero_le m) u).2
  have hplus := carrierSquareAmplitude_derivative_bound a b (B*R) (C*ε)
    (mul_nonneg hB.le hRp.le) ha hac hb hsa n ha0 (fun u => (hd n hn u).1) hb0 (-2*t) s
  have hminus := carrierSquareAmplitude_derivative_bound b a (B*R) (C*ε)
    (mul_nonneg hB.le hRp.le) hb hbc ha hsb n hb0 (fun u => (hd n hn u).2) ha0 (2*t) s
  constructor
  · change ‖iteratedDeriv n (carrierSquareAmplitude a b (-2*t)) s‖≤_
    convert hplus using 1
    ring
  · change ‖iteratedDeriv n (carrierSquareAmplitude b a (2*t)) s‖≤_
    convert hminus using 1
    ring

#print axioms windowSquareCarrier_regular
#print axioms windowTimeSquare_carriers
#print axioms windowSquareCarrier_uniform_bounds

end QuantitativeMaass
