module

public import QuantitativeMaassVolumeKernelUniformV1
public import QuantitativeMaassVolumeTraceLinearV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- Actual Hilbert-operator and spherical-symbol trace comparison, uniform
before the Hecke monomial degree and cosine time shift. -/
theorem mixedHeckeSymbol_volume_trace_error
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0<N) (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 2≤t → ∀ (S : Set ℍ),IsCompact S → S⊆Metric.closedBall o L → ∀ (n : ℕ) (τ : ℝ),
      |windowVolumeOperatorTrace N K he hc R (lt_of_lt_of_le zero_lt_one hR)
          (t-ε) (t+ε) S (mixedHeckeSymbol N p hN hpN a b hab n τ).1-
        volume.real S*
          windowSymbolIdentity p K R (t-ε) (t+ε) (mixedHeckeSymbol N p hN hpN a b hab n τ).2|≤
        (heckeWordErrorGrowth p)^n*C*(1+|τ|)*Real.sqrt t*ε^2*Real.exp (A*R+30*L+10*|τ|) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := upperTranslatedWindowKernel_volume_trace_error K he hc o
  refine ⟨A,C,hA,hC,?_⟩
  intro N p _ _ hN hpN hNp a b hab L R ε t hR hL hε hε1 ht S hS hSL n τ
  have hh := hbound τ N p L R ε t hR hL hε hε1 (by linarith : 1≤t) S hS hSL n
  change |windowVolumeOperatorTrace N K he hc R (lt_of_lt_of_le zero_lt_one hR)
    (t-ε) (t+ε) S
      (Wave.shiftedQuotientWave N τ*(HeckeL2.operator N p hN hpN a b hab)^n)-
    volume.real S*
      windowSymbolIdentity p K R (t-ε) (t+ε) (fun z => z.1^n*Real.cos (τ*z.2))|≤_
  rw [windowSymbolIdentity_monomial p K he hc R (lt_of_lt_of_le zero_lt_one hR)
    (t-ε) (t+ε) (by linarith) n τ]
  unfold windowVolumeOperatorTrace
  change |(∫ z in S,
    (inner ℂ (Wave.shiftedQuotientWave N τ (((HeckeL2.operator N p hN hpN a b hab)^n)
      (windowAbelColumn N K he hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z)))
      (windowAbelColumn N K he hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z)).re ∂volume)-_|≤_
  simp_rw [windowAbelColumn_wave_hecke_power τ N p hN hpN hNp a b hab]
  exact hh

#print axioms mixedHeckeSymbol_volume_trace_error
end QuantitativeMaass
