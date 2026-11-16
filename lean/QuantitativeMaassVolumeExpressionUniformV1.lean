module

public import QuantitativeMaassVolumeMonomialUniformV1
public import QuantitativeMaassMixedExpansionFunctionalV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

local instance (N : ℕ) : Ring (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.ring
local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.algebra

/-- Uniform trace error for the common finite operator/symbol expansion,
with explicit coefficient mass, degree and time support. -/
theorem mixedExpression_volume_trace_error
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0<N) (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 2≤t → ∀ (S : Set ℍ),IsCompact S → S⊆Metric.closedBall o L →
      ∀ (E : MixedExpansion.Expression) (m : ℕ) (T : ℝ),0≤T → MixedExpansion.Bounded m T E →
      let v := MixedExpansion.eval N p hN hpN a b hab E
      |windowVolumeOperatorTrace N K he hc R (lt_of_lt_of_le zero_lt_one hR)
          (t-ε) (t+ε) S v.1-
        volume.real S*windowSymbolIdentity p K R (t-ε) (t+ε) v.2|≤
        MixedExpansion.mass E*(max 1 (heckeWordErrorGrowth p))^m*C*(1+T)*Real.sqrt t*ε^2*
          Real.exp (A*R+30*L+10*T) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := mixedHeckeSymbol_volume_trace_error K he hc o
  refine ⟨A,C,hA,hC,?_⟩
  intro N p _ _ hN hpN hNp a b hab L R ε t hR hL hε hε1 ht S hS hSL E m T hT hE v
  let f : HeckeWavePair N→ℝ := fun u =>
    windowVolumeOperatorTrace N K he hc R (lt_of_lt_of_le zero_lt_one hR)
      (t-ε) (t+ε) S u.1-
    volume.real S*windowSymbolIdentity p K R (t-ε) (t+ε) u.2
  have h0 : f 0=0 := by
    simp only [f,Prod.fst_zero,Prod.snd_zero,windowVolumeOperatorTrace,zero_apply,
      inner_zero_left,Complex.zero_re,integral_zero,windowSymbolIdentity,finitePlaceSymbol,
      Pi.zero_apply,mul_zero,sub_zero]
  have hadd : ∀ u∈mixedHeckeSpan N p hN hpN a b hab,
      ∀ v∈mixedHeckeSpan N p hN hpN a b hab,f (u+v)=f u+f v := by
    intro u hu v hv
    dsimp only [f]
    rw [windowSymbolIdentity_add N p hN hpN a b hab K hK hm R (lt_of_lt_of_le zero_lt_one hR)
        (t-ε) (t+ε) (by linarith) (by linarith) hu hv]
    dsimp only [Prod.fst_add]
    rw [windowVolumeOperatorTrace_add N K he hc R (lt_of_lt_of_le zero_lt_one hR)
      (t-ε) (t+ε) _ hS]
    ring
  have hsmul : ∀ c : ℝ,∀ u∈mixedHeckeSpan N p hN hpN a b hab,f (c • u)=c*f u := by
    intro c u _
    change windowVolumeOperatorTrace N K he hc R (lt_of_lt_of_le zero_lt_one hR)
      (t-ε) (t+ε) S (c • u.1)-
      volume.real S*windowSymbolIdentity p K R (t-ε) (t+ε) (c • u.2)=_
    rw [windowVolumeOperatorTrace_smul,windowSymbolIdentity_smul]
    dsimp only [f]
    ring
  let B := (max 1 (heckeWordErrorGrowth p))^m*C*(1+T)*Real.sqrt t*ε^2*
    Real.exp (A*R+30*L+10*T)
  have hmono (u : MixedExpansion.Term) (hu : u∈E) :
      |f (mixedHeckeSymbol N p hN hpN a b hab u.degree u.time)|≤B := by
    have hb := hbound N p hN hpN hNp a b hab L R ε t hR hL hε hε1 ht S hS hSL u.degree u.time
    have hu' := hE u hu
    have hq : 0≤heckeWordErrorGrowth p := by unfold heckeWordErrorGrowth;positivity
    have hp : (heckeWordErrorGrowth p)^u.degree≤(max 1 (heckeWordErrorGrowth p))^m :=
      (pow_le_pow_left₀ hq (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hu'.1)
    apply hb.trans
    dsimp only [B]
    gcongr <;> exact hu'.2
  have hh := MixedExpansion.eval_functional_bound N p hN hpN a b hab f h0 hadd hsmul E B hmono
  convert hh using 1
  dsimp only [B]
  ring

#print axioms mixedExpression_volume_trace_error
end QuantitativeMaass
