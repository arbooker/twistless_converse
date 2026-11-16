module

public import QuantitativeMaassVolumeDeficitExponentialV1
public import QuantitativeMaassLVDeficitMainV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- The actual positive LV deficit trace over a compact volume set is
bounded by its inverse-square-root spherical deficit plus the explicit
geometric error. This is uniform before the compact cutoff and degree. -/
theorem actualLVDeficit_volume_trace_upper
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0<N) (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 2≤t →
      ∀ (S : Set ℍ),IsCompact S → S⊆Metric.closedBall o L → ∀ d : ℕ,0<d →
      windowVolumeOperatorTrace N K he hc R (lt_of_lt_of_le zero_lt_one hR)
        (t-ε) (t+ε) S (actualLVDeficit N p hN hpN a b hab d)≤
      volume.real S*lvSphericalDeficit p d*
        (windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re+
      C*Real.sqrt t*ε^2*Real.exp (A*R+30*L+
        (2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|)*(d:ℝ)) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := actualLVDeficit_volume_exponential_trace_error K he hc hK hm o
  refine ⟨A,C,hA,hC,?_⟩
  intro N p _ _ hN hpN hNp a b hab L R ε t hR hL hε hε1 ht S hS hSL d hd
  have hh := (abs_le.mp (hbound N p hN hpN hNp a b hab L R ε t hR hL hε hε1 ht S hS hSL d)).2
  have hs := (windowSymbolIdentity_deficit_bounds N p hN hpN a b hab K he hc hK hm
    R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (by linarith) (by linarith) d hd).2
  have hm := mul_le_mul_of_nonneg_left hs (measureReal_nonneg (μ:=volume) (s:=S))
  nlinarith only [hh,hm]

#print axioms actualLVDeficit_volume_trace_upper
end QuantitativeMaass
