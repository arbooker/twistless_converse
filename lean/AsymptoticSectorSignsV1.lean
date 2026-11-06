module

public import AsymptoticRamifiedCoefficientsV1
public import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
@[expose] public section

namespace AsymptoticSectorSigns

open Complex FinitenessOriginalInput
open scoped BigOperators

/-- The primes dividing the conductor exactly once. -/
def simplePrimes (N : ℕ) : Finset ℕ := N.primeFactors.filter (fun p => ¬p^2∣N)

theorem mem_simplePrimes {N p : ℕ} :
    p∈simplePrimes N ↔ p.Prime ∧ p∣N ∧ ¬p^2∣N := by
  simp only [simplePrimes,Finset.mem_filter,Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp,hpN,_⟩,hpsq⟩
    exact ⟨hp,hpN,hpsq⟩
  · rintro ⟨hp,hpN,hpsq⟩
    have hN : N≠0 := by rintro rfl; exact hpsq (dvd_zero _)
    exact ⟨⟨hp,hpN,hN⟩,hpsq⟩

/-- A geometric Fricke sign and one sign for each simple ramified prime.
The index type depends only on N, not on the weight or the observation set. -/
abbrev Sector (N : ℕ) := Bool × ({p // p∈simplePrimes N} → Bool)

def sign (b : Bool) : ℂ := if b then 1 else -1

theorem sign_sq (b : Bool) : sign b^2=1 := by cases b <;> norm_num [sign]
theorem sign_norm (b : Bool) : ‖sign b‖=1 := by cases b <;> norm_num [sign]

theorem sign_decide {z : ℂ} (hz : z=1 ∨ z= -1) :
    sign (by classical exact decide (z=1))=z := by
  classical
  rcases hz with rfl | rfl <;> norm_num [sign]

/-- Outside the simple ramified primes the value is irrelevant and set
to one. This permits the multiplier to be written as an ordinary product. -/
def delta {N : ℕ} (e : Sector N) (p : ℕ) : ℂ :=
  if hp : p∈simplePrimes N then sign (e.2 ⟨p,hp⟩) else 1

theorem delta_norm {N : ℕ} (e : Sector N) (p : ℕ) : ‖delta e p‖=1 := by
  unfold delta
  split_ifs <;> simp only [sign_norm,norm_one]

def multiplier {N : ℕ} (e : Sector N) (q : ℕ) : ℂ :=
  sign e.1 * ∏ p ∈ q.primeFactors.filter (fun p => p∣N ∧ ¬p^2∣N), -delta e p

theorem multiplier_norm {N : ℕ} (e : Sector N) (q : ℕ) : ‖multiplier e q‖=1 := by
  simp only [multiplier,norm_mul,sign_norm,norm_prod,norm_neg,delta_norm,Finset.prod_const_one,mul_one]

theorem multiplier_one {N : ℕ} (e : Sector N) : multiplier e 1=sign e.1 := by
  simp [multiplier]

theorem card (N : ℕ) : Fintype.card (Sector N)=2^((simplePrimes N).card+1) := by
  simp only [Sector,Fintype.card_prod,Fintype.card_bool,Fintype.card_fun,Fintype.card_coe]
  rw [pow_succ,mul_comm]

/-- The original Euler data determine all local signs and every positive
twist law in one fixed geometric sector. No sign is chosen independently
for a twist, even when the twist is identically zero. -/
theorem euler_sector {N h : ℕ} {f : ℕ → ℂ} (hN : 0<N)
    (hf : IsSolution N (2*(h+1)) f) :
    ∃ e : Sector N,
      (∀ p : ℕ, p∈simplePrimes N → delta e p=f p*(Real.sqrt p:ℂ)) ∧
      ∀ q : ℕ, 0<q → ∀ z : ℂ, 0<z.im →
        FinitenessAnalyticReconstruction.twist
          (FinitenessFourierConstruction.fourier
            (FinitenessOriginalFourier.fullCoefficients f (2*(h+1)))) q z=
        multiplier e q/((((Real.sqrt (Nat.lcm N (q^2)):ℝ):ℂ)*z)^(2*(h+1)))*
          FinitenessAnalyticReconstruction.twist
            (FinitenessFourierConstruction.fourier
              (FinitenessOriginalFourier.fullCoefficients f (2*(h+1))))
            q (-1/((Nat.lcm N (q^2):ℕ)*z)) := by
  classical
  obtain ⟨ε,hε,hFE⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  have heps : ε^2=1 := sq_eq_one_iff.mpr hε
  have hI : I^(2*(h+1))=(-1:ℂ)^(h+1) := by rw [pow_mul,I_sq]
  have hw : ε*I^(2*(h+1))=1 ∨ ε*I^(2*(h+1))= -1 := by
    apply sq_eq_one_iff.mp
    rw [mul_pow,heps,hI,pow_right_comm]
    norm_num
  let e : Sector N := ⟨decide (ε*I^(2*(h+1))=1),
    fun p => decide (f p.val*(Real.sqrt p.val:ℂ)=1)⟩
  have hd (p : ℕ) (hp : p∈simplePrimes N) : delta e p=f p*(Real.sqrt p:ℂ) := by
    obtain ⟨hp',hpN,hpsq⟩ := mem_simplePrimes.mp hp
    simp only [delta,dite_eq_left hp,e]
    exact sign_decide (AsymptoticRamifiedCoefficients.simple_sign hf.toEulerData hp' hpN hpsq)
  have hm (q : ℕ) : multiplier e q=
      FinitenessNormalizedTwistProduct.root N f q*ε*I^(2*(h+1)) := by
    rw [multiplier,AsymptoticRamifiedCoefficients.twist_root]
    have hprod : (∏ p ∈ q.primeFactors.filter (fun p => p∣N ∧ ¬p^2∣N), -delta e p)=
        ∏ p ∈ q.primeFactors.filter (fun p => p∣N ∧ ¬p^2∣N), -(f p*(Real.sqrt p:ℂ)) := by
      apply Finset.prod_congr rfl
      intro p hp
      obtain ⟨hpq,hpN,hpsq⟩ := Finset.mem_filter.mp hp
      rw [hd p (mem_simplePrimes.mpr ⟨Nat.prime_of_mem_primeFactors hpq,hpN,hpsq⟩)]
    rw [hprod,show sign e.1=ε*I^(2*(h+1)) from sign_decide hw]
    ring
  exact ⟨e,hd,fun q hq z hz => by rw [hm q]; exact hFE q hq z hz⟩

#print axioms card
#print axioms multiplier_norm
#print axioms euler_sector

end AsymptoticSectorSigns
