module

public import FinitenessRamanujanFourierV1
public import FinitenessRamanujanDivisorV1

set_option autoImplicit false
set_option maxHeartbeats 600000
@[expose] public section

namespace AsymptoticRamifiedFourier

open Complex FinitenessFourierConstruction FinitenessPolynomialSeries
open FinitenessRamanujanSum FinitenessRamanujanDivisor

theorem translated_height {p : ℕ} (hp : 0<p) {z : ℂ} (hz : 0<z.im) (a : ℕ) :
    0<((z+(a:ℂ))/(p:ℂ)).im := by
  have hp' : (0:ℝ)<p := by exact_mod_cast hp
  simpa only [← Complex.ofReal_natCast,Complex.div_ofReal_im,Complex.add_im,
    Complex.ofReal_im,add_zero] using div_pos hz hp'

theorem coefficient_sum (a : ℕ → ℂ) (p n : ℕ) (z : ℂ) :
    (∑ b ∈ Finset.range p,a n*Complex.exp (2*Real.pi*I*(n:ℂ)*((z+(b:ℂ))/p)))=
      (a n*complete p n)*Complex.exp (2*Real.pi*I*(n:ℂ)*(z/p)) := by
  rw [complete,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [show (z+(b:ℂ))/p=z/p+(b:ℂ)/p by ring,
    ← FinitenessRamanujanFourier.phase_translate]
  ring

/-- Full translation averaging extracts the coefficients divisible by p.
The convergence and the reindexing are part of the statement's proof. -/
theorem average (a : ℕ → ℂ) (ha : PolynomialBound a) {p : ℕ} (hp : 0<p)
    {z : ℂ} (hz : 0<z.im) :
    (∑ b ∈ Finset.range p,fourier a ((z+(b:ℂ))/p))=
      (p:ℂ)*fourier (fun n => a (p*n)) z := by
  have hs : ∀ b ∈ Finset.range p,Summable (fun n : ℕ =>
      a n*Complex.exp (2*Real.pi*I*(n:ℂ)*((z+(b:ℂ))/p))) :=
    fun b _ => FinitenessOriginalFourier.exp_summable ha (translated_height hp hz b)
  simp_rw [fourier_eq_exp]
  rw [← Summable.tsum_finsetSum hs]
  simp_rw [coefficient_sum,complete_eval hp]
  let f : ℕ → ℂ := fun n => (a n*(if p∣n then (p:ℂ) else 0))*
    Complex.exp (2*Real.pi*I*(n:ℂ)*(z/p))
  have hinj : Function.Injective (fun n : ℕ => p*n) := by
    intro n m he
    exact Nat.eq_of_mul_eq_mul_left hp he
  have hsupp : Function.support f⊆Set.range (fun n : ℕ => p*n) := by
    intro n hn
    have hd : p∣n := by
      by_contra h
      exact hn (by simp [f,h])
    obtain ⟨m,hm⟩ := hd
    exact ⟨m,hm.symm⟩
  change (∑' n,f n)=_
  rw [← hinj.tsum_eq hsupp,← tsum_mul_left]
  apply tsum_congr
  intro n
  have hp' : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  dsimp [f]
  rw [ite_eq_left (dvd_mul_right p n)]
  have he : 2*Real.pi*I*((p*n:ℕ):ℂ)*(z/p)=2*Real.pi*I*(n:ℂ)*z := by
    push_cast
    field_simp
  rw [he]
  ring

/-- The literal ramified coefficient row implies the averaging equation. -/
theorem average_of_row (a : ℕ → ℂ) (ha : PolynomialBound a) {p : ℕ} (hp : 0<p)
    (c : ℂ) (hc : ∀ n,a (p*n)=c*a n) {z : ℂ} (hz : 0<z.im) :
    (∑ b ∈ Finset.range p,fourier a ((z+(b:ℂ))/p))=(p:ℂ)*c*fourier a z := by
  rw [average a ha hp hz]
  simp_rw [fourier_eq_exp,hc,mul_assoc]
  rw [tsum_mul_left]

#print axioms average
#print axioms average_of_row

end AsymptoticRamifiedFourier
