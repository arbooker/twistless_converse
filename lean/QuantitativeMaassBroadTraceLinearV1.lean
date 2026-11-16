module

public import QuantitativeMaassBroadSphericalWeightV1
public import QuantitativeMaassBroadHeckeTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap

namespace QuantitativeMaass

def broadVolumeOperatorTrace (N : ℕ) [NeZero N] (L : ℝ) (hL : 0 < L) (t : ℝ)
    (K : Set ℍ) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) : ℝ :=
  ∫ z in K, (inner ℂ (A (broadAbelColumn N L hL t z)) (broadAbelColumn N L hL t z)).re

def broadSymbolIdentity (p : ℕ) (L t : ℝ) (F : (ℝ × ℝ) → ℝ) : ℝ :=
  1/(4*Real.pi)*(∫ r : ℝ, broadSpectralWeight L t r*finitePlaceSymbol p F r)

theorem broadVolumeOperatorTrace_integrable (N : ℕ) [NeZero N]
    (L : ℝ) (hL : 0 < L) (t : ℝ) (K : Set ℍ) (hK : IsCompact K)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    IntegrableOn (fun z => (inner ℂ (A (broadAbelColumn N L hL t z))
      (broadAbelColumn N L hL t z)).re) K := by
  have hc := broadAbelColumn_continuous N L hL t
  exact (Complex.continuous_re.comp ((A.continuous.comp hc).inner hc)).continuousOn.integrableOn_compact hK

theorem broadVolumeOperatorTrace_add (N : ℕ) [NeZero N]
    (L : ℝ) (hL : 0 < L) (t : ℝ) (K : Set ℍ) (hK : IsCompact K)
    (A B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    broadVolumeOperatorTrace N L hL t K (A+B) =
      broadVolumeOperatorTrace N L hL t K A + broadVolumeOperatorTrace N L hL t K B := by
  unfold broadVolumeOperatorTrace
  simp only [add_apply, inner_add_left, Complex.add_re]
  exact integral_add (broadVolumeOperatorTrace_integrable N L hL t K hK A)
    (broadVolumeOperatorTrace_integrable N L hL t K hK B)

theorem broadVolumeOperatorTrace_smul (N : ℕ) [NeZero N]
    (L : ℝ) (hL : 0 < L) (t : ℝ) (K : Set ℍ)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (c : ℝ) :
    broadVolumeOperatorTrace N L hL t K (c • A) = c*broadVolumeOperatorTrace N L hL t K A := by
  unfold broadVolumeOperatorTrace
  have hh (z : ℍ) : inner ℂ (c • A (broadAbelColumn N L hL t z))
      (broadAbelColumn N L hL t z) =
      c • inner ℂ (A (broadAbelColumn N L hL t z)) (broadAbelColumn N L hL t z) :=
    inner_smul_left_eq_smul (𝕜 := ℂ)
      (A (broadAbelColumn N L hL t z)) (broadAbelColumn N L hL t z) c
  simp only [smul_apply, hh, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact integral_const_mul _ _

theorem broadSymbolIdentity_monomial (p : ℕ) [Fact p.Prime]
    (L : ℝ) (hL : 0 < L) (t : ℝ) (n : ℕ) (τ : ℝ) :
    broadSymbolIdentity p L t (fun z => z.1^n*Real.cos (τ*z.2)) =
      (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
        (broadTranslatedProfile L hL t τ 1).re := by
  rw [broadTranslatedProfile_eq_mass]
  simp only [Complex.ofReal_re, broadSymbolIdentity]
  simp_rw [finitePlaceSymbol_monomial]
  have heq : (fun r => broadSpectralWeight L t r*
      ((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*Real.cos (τ*r))) =
      fun r => ((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ))*
        (Real.cos (τ*r)*broadSpectralWeight L t r) := by
    funext r
    ring
  rw [heq, integral_const_mul]
  ring

theorem broadSymbolIdentity_add (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬p∣N) (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (L : ℝ) (hL : 0 < L) (t : ℝ)
    {u v : HeckeWavePair N} (hu : u ∈ mixedHeckeSpan N p hN hpN a b hab)
    (hv : v ∈ mixedHeckeSpan N p hN hpN a b hab) :
    broadSymbolIdentity p L t (u+v).2 = broadSymbolIdentity p L t u.2 + broadSymbolIdentity p L t v.2 := by
  unfold broadSymbolIdentity
  rw [Prod.snd_add, finitePlaceSymbol_add p u.2 v.2
    (mixedHeckeSpan_symbol_continuous N p hN hpN a b hab hu)
    (mixedHeckeSpan_symbol_continuous N p hN hpN a b hab hv)]
  simp only [Pi.add_apply, mul_add]
  rw [integral_add
    (mixedHeckeSpan_weight_integrable N p hN hpN a b hab _ (broadSpectralWeight_integrable L hL t) hu)
    (mixedHeckeSpan_weight_integrable N p hN hpN a b hab _ (broadSpectralWeight_integrable L hL t) hv), mul_add]

theorem broadSymbolIdentity_smul (p : ℕ) (L t : ℝ) (F : (ℝ × ℝ) → ℝ) (c : ℝ) :
    broadSymbolIdentity p L t (c • F) = c*broadSymbolIdentity p L t F := by
  unfold broadSymbolIdentity
  rw [finitePlaceSymbol_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (broadSpectralWeight L t _) c]
  rw [integral_const_mul]
  ring

#print axioms broadVolumeOperatorTrace_add
#print axioms broadVolumeOperatorTrace_smul
#print axioms broadSymbolIdentity_monomial
#print axioms broadSymbolIdentity_add
#print axioms broadSymbolIdentity_smul

end QuantitativeMaass
