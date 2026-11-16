module

public import QuantitativeMaassLVGrowingTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- Fixed-prime exponential envelope for the literal LV expansion cost. -/
theorem lv_degree_cost_bound (g b : ℝ) (hg : 0≤g) (hb : 0≤b) (d : ℕ) :
    (2*(2:ℝ)^d)*g^(2*d)*(1+2*(d:ℝ)*b)*Real.exp (20*(d:ℝ)*b)≤
      2*Real.exp ((2+2*g+22*b)*(d:ℝ)) := by
  have h2 : (2:ℝ)≤Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have hg' : g≤Real.exp g := by linarith [Real.add_one_le_exp g]
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) h2 d
  have hpowg := pow_le_pow_left₀ hg hg' (2*d)
  rw [←Real.exp_nat_mul] at hpow hpowg
  have hlin : 1+2*(d:ℝ)*b≤Real.exp (2*(d:ℝ)*b) := by
    simpa only [add_comm] using Real.add_one_le_exp (2*(d:ℝ)*b)
  calc
    _ ≤ (2*Real.exp ((d:ℝ)*2))*Real.exp (((2*d:ℕ):ℝ)*g)*
        Real.exp (2*(d:ℝ)*b)*Real.exp (20*(d:ℝ)*b) := by gcongr
    _ = _ := by
      push_cast
      rw [mul_assoc,←Real.exp_add,mul_assoc,←Real.exp_add,mul_assoc,←Real.exp_add]
      congr 2
      ring

/-- A simpler degree-uniform error bound for the actual LV operator. -/
theorem actualLVFilter_exponential_trace_error
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0<N) (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 2≤t → ∀ d : ℕ,
      |windowLocalOperatorTrace N K he hc R (lt_of_lt_of_le zero_lt_one hR)
          (t-ε) (t+ε) (Metric.closedBall o L) (actualLVFilter N p hN hpN a b hab d)-
        (quotientMeasure N).real (Metric.closedBall o L)*
          windowSymbolIdentity p K R (t-ε) (t+ε) (lvScalarSymbol p d)|≤
        C*Real.sqrt t*ε^2*Real.exp (A*R+30*L+
          (2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|)*(d:ℝ)) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := actualLVFilter_growing_trace_error K he hc hK hm o
  refine ⟨A,2*C,hA,by positivity,?_⟩
  intro N p _ _ hN hpN hNp a b hab L R ε t hR hL hε hε1 ht d
  apply (hbound N p hN hpN hNp a b hab L R ε t hR hL hε hε1 ht d).trans
  have hh := mul_le_mul_of_nonneg_right
    (lv_degree_cost_bound (max 1 (heckeWordErrorGrowth p)) |Real.log p|
      (le_trans zero_le_one (le_max_left _ _)) (abs_nonneg _) d)
    (show 0≤C*Real.sqrt t*ε^2*Real.exp (A*R+30*L) by positivity)
  simp only [Real.exp_add] at hh ⊢
  convert hh using 1 <;> ring

#print axioms lv_degree_cost_bound
#print axioms actualLVFilter_exponential_trace_error
end QuantitativeMaass
