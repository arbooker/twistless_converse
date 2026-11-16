module

public import QuantitativeMaassRepeatedNewEquationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticFreshMatrices AsymptoticFreshResidues AsymptoticFreshAveraging
open AsymptoticIntegralSubgroup AsymptoticOrbitDecode AsymptoticRamifiedTwistedLaw

namespace QuantitativeMaass

/-- The prime Ramanujan sum as a literal finite sum of translations. -/
def primeTranslationSum (p : ℕ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  ∑ i : Fin (p-1),f (primeLabels p i • z)

/-- At a good prime, modularity and Fricke alone give the twisted
reflection law by the explicit residue permutation. -/
theorem good_prime_twist_of_modular (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (f : ℍ → ℂ)
    (hmod : ∀ a : gamma N,∀ z,f (a.val • z)=f z)
    (w : ℂ) (hW : ∀ z,w*f (frickeLabel N hN • z)=f z) (z : ℍ) :
    w*primeTranslationSum p f
      (frickeLabel (p*(p*N)) (Nat.mul_pos (Fact.out : p.Prime).pos
        (Nat.mul_pos (Fact.out : p.Prime).pos hN)) • z)=primeTranslationSum p f z := by
  have hd (i : Fin (p-1)) (y : ℍ) : w*f (defectLabel N p hN hpN i • y)=f y := by
    rw [defectLabel,label_eq_fricke_canonical N p hN (Fact.out : p.Prime).pos
      ((permutation p N hpN i).val+1) (i.val+1) (quotient p N hpN i)
      (quotient_relation p N hpN i),mul_smul,hW,←canonical_label]
    exact hmod ⟨_,⟨_,canonical_mem_Gamma0 N p _ _ _ _,rfl⟩⟩ y
  have he : (∑ i : Fin (p-1),w*f (reflectedLabel N p hN i • z))=
      ∑ i : Fin (p-1),f (primeLabels p i • z) := by
    rw [←Equiv.sum_comp (permutation p N hpN) (fun i => w*f (reflectedLabel N p hN i • z))]
    apply Finset.sum_congr rfl
    intro i _
    rw [←defectLabel_translation N p hN hpN,mul_smul,hd]
  simpa only [primeTranslationSum,reflectedLabel_eq,mul_smul,Finset.mul_sum] using he

/-- At a prime occurring once, the ramified U_p law gives the twisted
Fricke identity, with its exact extra factor of p in the conductor. -/
theorem simple_prime_twist_of_ramified (N p : ℕ) (hN : 0<N) (hp : 0<p)
    (f : ℍ → ℂ) (w δ : ℂ) (hδ : δ^2=1)
    (hW : ∀ z,w*f (frickeLabel N hN • z)=f z)
    (hU : ∀ z,∑ a : Fin p,f (ramifiedLabel p hp a • z)=δ*f z)
    (z : ℍ) :
    primeTranslationSum p f (frickeLabel (p*N) (Nat.mul_pos hp hN) • z)=
      (-w*δ)*primeTranslationSum p f z := by
  have he := punctured_fricke N p hN hp (fun g : AsymptoticRationalGroup.Group => f (g • z))
    w δ hδ (fun g => by simpa only [mul_smul] using hW (g • z))
    (fun g => by simpa only [mul_smul] using hU (g • z)) 1
  simpa only [puncturedSum_eq_primeLabels p hp,mul_one,one_smul,mul_smul,primeTranslationSum] using he

/-- The vanishing ramified row makes the prime Ramanujan sum minus the
original function, so its reflected conductor stays N at repeated primes. -/
theorem repeated_prime_twist_of_ramified_zero (N p : ℕ) (hN : 0<N) (hp : 0<p)
    (f : ℍ → ℂ) (w : ℂ)
    (hW : ∀ z,w*f (frickeLabel N hN • z)=f z)
    (hU : ∀ z,∑ a : Fin p,f (ramifiedLabel p hp a • z)=0)
    (z : ℍ) : w*primeTranslationSum p f (frickeLabel N hN • z)=primeTranslationSum p f z := by
  have ht (y : ℍ) : primeTranslationSum p f y=-f y := by
    have he := residueSum_of_ramified p hp (fun g : AsymptoticRationalGroup.Group => f (g • y))
      0 (fun g => by simpa only [mul_smul,zero_mul] using hU (g • y)) 1
    have hs := puncturedSum_eq_primeLabels p hp
      (fun g : AsymptoticRationalGroup.Group => f (g • y)) 1
    simp only [puncturedSum,he,zero_mul,one_smul,mul_one,zero_sub] at hs
    exact hs.symm
  rw [ht,ht,mul_neg,hW]

#print axioms good_prime_twist_of_modular
#print axioms simple_prime_twist_of_ramified
#print axioms repeated_prime_twist_of_ramified_zero

end QuantitativeMaass
