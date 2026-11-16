module

public import QuantitativeMaassMixedHeckeDensityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- The actual local Hilbert trace formed from the canonical moving-window columns. -/
def windowLocalOperatorTrace (N : ℕ) [NeZero N] (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) : ℝ :=
  ∫ x in S,(inner ℂ (A (windowAbelColumn N K he hc R hR a b x))
    (windowAbelColumn N K he hc R hR a b x)).re ∂quotientMeasure N

/-- The original squared spectral window, integrated against a joint symbol. -/
def windowSymbolIdentity (p : ℕ) (K : SchwartzMap ℝ ℝ) (R a b : ℝ)
    (F : (ℝ × ℝ) → ℝ) : ℝ :=
  1/(4*Real.pi)*(∫ r,(smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2*
    windowPlancherelWeight r*finitePlaceSymbol p F r)

theorem windowLocalOperatorTrace_integrable (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (hS : IsCompact S)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    IntegrableOn (fun x => (inner ℂ (A (windowAbelColumn N K he hc R hR a b x))
      (windowAbelColumn N K he hc R hR a b x)).re) S (quotientMeasure N) := by
  have hcol := windowAbelColumn_continuous N K he hc R hR a b
  exact (Complex.continuous_re.comp ((A.continuous.comp hcol).inner hcol)).continuousOn.integrableOn_compact hS

theorem windowLocalOperatorTrace_add (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (hS : IsCompact S)
    (A B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    windowLocalOperatorTrace N K he hc R hR a b S (A+B)=
      windowLocalOperatorTrace N K he hc R hR a b S A+
      windowLocalOperatorTrace N K he hc R hR a b S B := by
  unfold windowLocalOperatorTrace
  simp only [add_apply,inner_add_left,Complex.add_re]
  exact integral_add (windowLocalOperatorTrace_integrable N K he hc R hR a b S hS A)
    (windowLocalOperatorTrace_integrable N K he hc R hR a b S hS B)

theorem windowLocalOperatorTrace_smul (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (c : ℝ) :
    windowLocalOperatorTrace N K he hc R hR a b S (c • A)=
      c*windowLocalOperatorTrace N K he hc R hR a b S A := by
  unfold windowLocalOperatorTrace
  have hh (x : ℍ) : inner ℂ (c • A (windowAbelColumn N K he hc R hR a b x))
      (windowAbelColumn N K he hc R hR a b x)=
      c • inner ℂ (A (windowAbelColumn N K he hc R hR a b x))
      (windowAbelColumn N K he hc R hR a b x) :=
    inner_smul_left_eq_smul (𝕜 := ℂ)
      (A (windowAbelColumn N K he hc R hR a b x)) (windowAbelColumn N K he hc R hR a b x) c
  simp only [smul_apply,hh,Complex.smul_re]
  exact integral_const_mul _ _

theorem windowSymbolIdentity_monomial (p : ℕ) [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (ha : 0<a) (n : ℕ) (τ : ℝ) :
    windowSymbolIdentity p K R a b (fun z => z.1^n*Real.cos (τ*z.2))=
      (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
        (translatedWindowIdentity τ K hc R hR a b).re := by
  rw [translatedWindowIdentity_eq_mass τ K he hc R hR a b ha]
  simp only [Complex.ofReal_re,windowSymbolIdentity]
  simp_rw [finitePlaceSymbol_monomial]
  have heq : (fun r => (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2*
      windowPlancherelWeight r*((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*Real.cos (τ*r)))=
      (fun r => ((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ))*
        (Real.cos (τ*r)*((smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2*windowPlancherelWeight r))) := by
    funext r;ring
  rw [heq,integral_const_mul]
  ring

theorem windowSymbolIdentity_add (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (a₀ b₀ : ℤ) (hab₀ : (p:ℤ)*a₀+(N:ℤ)*b₀=1)
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) (hab : a≤b)
    {u v : HeckeWavePair N} (hu : u∈mixedHeckeSpan N p hN hpN a₀ b₀ hab₀)
    (hv : v∈mixedHeckeSpan N p hN hpN a₀ b₀ hab₀) :
    windowSymbolIdentity p K R a b (u+v).2=
      windowSymbolIdentity p K R a b u.2+windowSymbolIdentity p K R a b v.2 := by
  have hw := (symmetric_squaredWindow_plancherel_mass a b ha hab K hK hm R hR).1
  unfold windowSymbolIdentity
  rw [Prod.snd_add,finitePlaceSymbol_add p u.2 v.2
    (mixedHeckeSpan_symbol_continuous N p hN hpN a₀ b₀ hab₀ hu)
    (mixedHeckeSpan_symbol_continuous N p hN hpN a₀ b₀ hab₀ hv)]
  simp only [Pi.add_apply,mul_add]
  rw [integral_add (mixedHeckeSpan_weight_integrable N p hN hpN a₀ b₀ hab₀ _ hw hu)
    (mixedHeckeSpan_weight_integrable N p hN hpN a₀ b₀ hab₀ _ hw hv),mul_add]

theorem windowSymbolIdentity_smul (p : ℕ) (K : SchwartzMap ℝ ℝ) (R a b : ℝ)
    (F : (ℝ × ℝ) → ℝ) (c : ℝ) :
    windowSymbolIdentity p K R a b (c • F)=c*windowSymbolIdentity p K R a b F := by
  unfold windowSymbolIdentity
  rw [finitePlaceSymbol_smul]
  simp only [Pi.smul_apply,smul_eq_mul]
  simp_rw [mul_left_comm _ c]
  rw [integral_const_mul]
  ring

#print axioms windowLocalOperatorTrace_integrable
#print axioms windowLocalOperatorTrace_add
#print axioms windowLocalOperatorTrace_smul
#print axioms windowSymbolIdentity_monomial
#print axioms windowSymbolIdentity_add
#print axioms windowSymbolIdentity_smul

end QuantitativeMaass
