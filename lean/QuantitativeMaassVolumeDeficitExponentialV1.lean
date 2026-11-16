module

public import QuantitativeMaassVolumeDeficitGrowingTraceV1
public import QuantitativeMaassLVExponentialCostV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- A simpler degree-uniform error bound for the actual positive LV deficit. -/
theorem actualLVDeficit_volume_exponential_trace_error
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0<N) (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 2≤t → ∀ (S : Set ℍ),IsCompact S → S⊆Metric.closedBall o L → ∀ d : ℕ,
      |windowVolumeOperatorTrace N K he hc R (lt_of_lt_of_le zero_lt_one hR)
          (t-ε) (t+ε) S (actualLVDeficit N p hN hpN a b hab d)-
        volume.real S*
          windowSymbolIdentity p K R (t-ε) (t+ε) (fun z => 1-lvScalarSymbol p d z)|≤
        C*Real.sqrt t*ε^2*Real.exp (A*R+30*L+
          (2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|)*(d:ℝ)) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := actualLVDeficit_volume_growing_trace_error K he hc hK hm o
  refine ⟨A,2*C,hA,by positivity,?_⟩
  intro N p _ _ hN hpN hNp a b hab L R ε t hR hL hε hε1 ht S hS hSL d
  apply (hbound N p hN hpN hNp a b hab L R ε t hR hL hε hε1 ht S hS hSL d).trans
  have hh := mul_le_mul_of_nonneg_right
    (lv_degree_cost_bound (max 1 (heckeWordErrorGrowth p)) |Real.log p|
      (le_trans zero_le_one (le_max_left _ _)) (abs_nonneg _) d)
    (show 0≤C*Real.sqrt t*ε^2*Real.exp (A*R+30*L) by positivity)
  simp only [Real.exp_add] at hh ⊢
  convert hh using 1 <;> ring

#print axioms actualLVDeficit_volume_exponential_trace_error
end QuantitativeMaass
