module

public import QuantitativeMaassVolumeExpressionUniformV1
public import QuantitativeMaassLVDeficitExpansionV1
public import QuantitativeMaassLVGeometricLowerV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- The actual positive LV deficit has an explicit trace error
uniform in its degree. The spherical symbol is evaluated from the same
finite expansion as the Hilbert operator. -/
theorem actualLVDeficit_volume_growing_trace_error
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
        (2*(2:ℝ)^d)*(max 1 (heckeWordErrorGrowth p))^(2*d)*C*
          (1+2*(d:ℝ)*|Real.log p|)*Real.sqrt t*ε^2*
          Real.exp (A*R+30*L+20*(d:ℝ)*|Real.log p|) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := mixedExpression_volume_trace_error K he hc hK hm o
  refine ⟨A,C,hA,hC,?_⟩
  intro N p _ _ hN hpN hNp a b hab L R ε t hR hL hε hε1 ht S hS hSL d
  obtain ⟨hmass,hdegree⟩ := MixedExpansion.deficitExpression_bounds p d
  have hh := hbound N p hN hpN hNp a b hab L R ε t hR hL hε hε1 ht S hS hSL
    (MixedExpansion.deficitExpression p d) (2*d) (2*(d:ℝ)*|Real.log p|) (by positivity) hdegree
  rw [MixedExpansion.eval_deficitExpression] at hh
  change |windowVolumeOperatorTrace N K he hc R (lt_of_lt_of_le zero_lt_one hR)
    (t-ε) (t+ε) S (actualLVDeficit N p hN hpN a b hab d)-
    volume.real S*
      windowSymbolIdentity p K R (t-ε) (t+ε) (fun z => 1-lvScalarSymbol p d z)|≤_ at hh
  apply hh.trans
  rw [show 10*(2*(d:ℝ)*|Real.log p|)=20*(d:ℝ)*|Real.log p| by ring]
  gcongr

#print axioms actualLVDeficit_volume_growing_trace_error
end QuantitativeMaass
