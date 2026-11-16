module

public import QuantitativeMaassTranslatedIdentityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- An actual Hilbert operator paired with its real finite-place/wave symbol. -/
abbrev HeckeWavePair (N : ℕ) :=
  (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) × ((ℝ × ℝ) → ℝ)

local instance (N : ℕ) : Ring (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  ContinuousLinearMap.ring

local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  ContinuousLinearMap.algebra

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)

/-- Both evaluations of the same basic wave-Hecke monomial. -/
def mixedHeckeSymbol (n : ℕ) (τ : ℝ) : HeckeWavePair N :=
  (Wave.shiftedQuotientWave N τ*(HeckeL2.operator N p hN hpN a b hab)^n,
    fun z => z.1^n*Real.cos (τ*z.2))

/-- Finite real linear combinations, retaining actual operator and scalar
symbol together so their coefficients cannot be chosen independently. -/
def mixedHeckeSpan : Submodule ℝ (HeckeWavePair N) :=
  Submodule.span ℝ (Set.range (fun z : ℕ × ℝ => mixedHeckeSymbol N p hN hpN a b hab z.1 z.2))

theorem mixedHeckeSymbol_mem (n : ℕ) (τ : ℝ) :
    mixedHeckeSymbol N p hN hpN a b hab n τ∈mixedHeckeSpan N p hN hpN a b hab :=
  Submodule.subset_span ⟨(n,τ),rfl⟩

/-- Product-to-sum holds simultaneously for the genuine commuting Hilbert
operators and the scalar symbols. -/
theorem mixedHeckeSymbol_mul (n m : ℕ) (s t : ℝ) :
    mixedHeckeSymbol N p hN hpN a b hab n s*mixedHeckeSymbol N p hN hpN a b hab m t=
      (1/2:ℝ) • (mixedHeckeSymbol N p hN hpN a b hab (n+m) (s+t)+
        mixedHeckeSymbol N p hN hpN a b hab (n+m) (s-t)) := by
  apply Prod.ext
  · change (Wave.shiftedQuotientWave N s*(HeckeL2.operator N p hN hpN a b hab)^n)*
      (Wave.shiftedQuotientWave N t*(HeckeL2.operator N p hN hpN a b hab)^m)=_
    have hc := (QuantitativeArithmeticMaassHecke.hecke_shiftedWave_commute N p hN hpN a b hab t).pow_left n
    have hw : Wave.shiftedQuotientWave N s*Wave.shiftedQuotientWave N t=
        (1/2:ℝ) • (Wave.shiftedQuotientWave N (s+t)+Wave.shiftedQuotientWave N (s-t)) := by
      rw [Wave.shiftedQuotientWave_cosine]
      module
    calc
      _ = (Wave.shiftedQuotientWave N s*Wave.shiftedQuotientWave N t)*
          ((HeckeL2.operator N p hN hpN a b hab)^n*(HeckeL2.operator N p hN hpN a b hab)^m) := by
        rw [mul_assoc,← mul_assoc ((HeckeL2.operator N p hN hpN a b hab)^n),hc.eq]
        simp only [mul_assoc]
      _ = _ := by
        rw [← pow_add,hw,smul_mul_assoc,add_mul]
        rfl
  · funext z
    change (z.1^n*Real.cos (s*z.2))*(z.1^m*Real.cos (t*z.2))=
      (1/2:ℝ)*(z.1^(n+m)*Real.cos ((s+t)*z.2)+z.1^(n+m)*Real.cos ((s-t)*z.2))
    rw [pow_add,add_mul,sub_mul,Real.cos_add,Real.cos_sub]
    ring

/-- The finite mixed span is closed under multiplication; this is a finite
algebra statement, with no completion or spectral realization premise. -/
theorem mixedHeckeSpan_mul_mem {u v : HeckeWavePair N}
    (hu : u∈mixedHeckeSpan N p hN hpN a b hab)
    (hv : v∈mixedHeckeSpan N p hN hpN a b hab) :
    u*v∈mixedHeckeSpan N p hN hpN a b hab := by
  induction hu,hv using Submodule.span_induction₂ with
  | mem_mem u v hu hv =>
    obtain ⟨⟨n,s⟩,rfl⟩ := hu
    obtain ⟨⟨m,t⟩,rfl⟩ := hv
    rw [mixedHeckeSymbol_mul]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (mixedHeckeSymbol_mem N p hN hpN a b hab _ _)
      (mixedHeckeSymbol_mem N p hN hpN a b hab _ _))
  | zero_left v hv => simpa only [zero_mul] using (mixedHeckeSpan N p hN hpN a b hab).zero_mem
  | zero_right u hu => simpa only [mul_zero] using (mixedHeckeSpan N p hN hpN a b hab).zero_mem
  | add_left u₁ u₂ v hu₁ hu₂ hv h₁ h₂ =>
    simpa only [add_mul] using (mixedHeckeSpan N p hN hpN a b hab).add_mem h₁ h₂
  | add_right u v₁ v₂ hu hv₁ hv₂ h₁ h₂ =>
    simpa only [mul_add] using (mixedHeckeSpan N p hN hpN a b hab).add_mem h₁ h₂
  | smul_left c u v hu hv h =>
    simpa only [smul_mul_assoc] using (mixedHeckeSpan N p hN hpN a b hab).smul_mem c h
  | smul_right c u v hu hv h =>
    simpa only [mul_smul_comm] using (mixedHeckeSpan N p hN hpN a b hab).smul_mem c h

theorem mixedHeckeSpan_one : (1:HeckeWavePair N)∈mixedHeckeSpan N p hN hpN a b hab := by
  have hh := mixedHeckeSymbol_mem N p hN hpN a b hab 0 0
  have heq : mixedHeckeSymbol N p hN hpN a b hab 0 0=(1:HeckeWavePair N) := by
    apply Prod.ext
    · simp only [mixedHeckeSymbol,pow_zero,mul_one,Wave.shiftedQuotientWave_zero]
      rfl
    · funext z
      simp only [mixedHeckeSymbol,pow_zero,zero_mul,Real.cos_zero,one_mul]
      rfl
  rwa [heq] at hh

/-- The genuine LV filter and its exact scalar polynomial belong to the same
finite mixed span. In particular, they admit one common finite expansion. -/
theorem actualLVFilter_symbol_mem (d : ℕ) :
    (actualLVFilter N p hN hpN a b hab d,
      fun z : ℝ × ℝ => 1-(1-(z.1-2*Real.cos (Real.log p*z.2))^2/(lvBound p)^2)^d)
      ∈mixedHeckeSpan N p hN hpN a b hab := by
  let S := mixedHeckeSpan N p hN hpN a b hab
  have hpow {v : HeckeWavePair N} (hv : v∈S) (k : ℕ) : v^k∈S := by
    induction k with
    | zero => simpa only [pow_zero] using mixedHeckeSpan_one N p hN hpN a b hab
    | succ k ih => rw [pow_succ];exact mixedHeckeSpan_mul_mem N p hN hpN a b hab ih hv
  let D : HeckeWavePair N := (lvDifference N p hN hpN a b hab,
    fun z => z.1-2*Real.cos (Real.log p*z.2))
  have hD : D∈S := by
    have heq : D=mixedHeckeSymbol N p hN hpN a b hab 1 0-
        (2:ℝ) • mixedHeckeSymbol N p hN hpN a b hab 0 (Real.log p) := by
      apply Prod.ext
      · change lvDifference N p hN hpN a b hab=_
        simp only [lvDifference,mixedHeckeSymbol,pow_one,pow_zero,mul_one,Wave.shiftedQuotientWave_zero]
        rfl
      · funext z
        change z.1-2*Real.cos (Real.log p*z.2)=
          z.1^1*Real.cos (0*z.2)-2*(z.1^0*Real.cos (Real.log p*z.2))
        simp only [pow_one,pow_zero,zero_mul,Real.cos_zero,mul_one,one_mul]
    rw [heq]
    exact S.sub_mem (mixedHeckeSymbol_mem N p hN hpN a b hab _ _)
      (S.smul_mem _ (mixedHeckeSymbol_mem N p hN hpN a b hab _ _))
  have hh := S.sub_mem (mixedHeckeSpan_one N p hN hpN a b hab)
    (hpow (S.sub_mem (mixedHeckeSpan_one N p hN hpN a b hab)
      (S.smul_mem ((lvBound p)^2)⁻¹ (hpow hD 2))) d)
  convert hh using 1
  apply Prod.ext
  · rfl
  · funext z
    change 1-(1-(z.1-2*Real.cos (Real.log p*z.2))^2/(lvBound p)^2)^d=
      1-(1-((lvBound p)^2)⁻¹*(z.1-2*Real.cos (Real.log p*z.2))^2)^d
    rw [div_eq_mul_inv,mul_comm ((lvBound p)^2)⁻¹]

#print axioms mixedHeckeSymbol_mem
#print axioms mixedHeckeSymbol_mul
#print axioms mixedHeckeSpan_mul_mem
#print axioms mixedHeckeSpan_one
#print axioms actualLVFilter_symbol_mem

end QuantitativeMaass
