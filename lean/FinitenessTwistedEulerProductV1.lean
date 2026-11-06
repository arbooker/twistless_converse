module

public import FinitenessTwistedPrimeFactorV1
public import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section

set_option autoImplicit false

namespace FinitenessTwistedEulerProduct

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessOriginalTwistLocal
  FinitenessEulerIdentification FinitenessEulerCoefficients FinitenessTwistedPrimeFactor

noncomputable def localMultiplier (N : ℕ) (f : ℕ → ℂ) (s : ℂ) (p α : ℕ) : ℂ :=
  if α=0 then 1 else D N f p (α-1) ((p:ℂ)^(-s))

noncomputable def multiplier (N : ℕ) (f : ℕ → ℂ) (q : ℕ) (s : ℂ) : ℂ :=
  q.factorization.prod (localMultiplier N f s)

theorem multiplier_prime_pow {p : ℕ} (hp : p.Prime) (j N : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    multiplier N f (p^(j+1)) s=D N f p j ((p:ℂ)^(-s)) := by
  unfold multiplier
  rw [hp.factorization_pow,Finsupp.prod_single_index (by simp [localMultiplier])]
  simp [localMultiplier]

theorem multiplier_mul {q r : ℕ} (hc : q.Coprime r) (N : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    multiplier N f (q*r) s=multiplier N f q s*multiplier N f r s := by
  unfold multiplier
  rw [Nat.factorization_mul_of_coprime hc]
  exact Finsupp.prod_add_index_of_disjoint hc.disjoint_primeFactors _

theorem twist_one (f : ℕ → ℂ) : twistCoefficients f 1=f := by
  funext n
  simp [twistCoefficients,FinitenessRamanujanSum.complexSum,
    FinitenessRamanujanSum.residues,FinitenessRamanujanSum.phase]

theorem twist_eq (f : ℕ → ℂ) (q : ℕ) :
    twistCoefficients f q=
      fun n => (FinitenessRamanujanFourier.twisted f q n:ℂ) := by
  funext n
  simp only [twistCoefficients,FinitenessRamanujanFourier.twisted,
    FinitenessRamanujanSum.ofReal_ramanujan]

theorem twisted_summable {f : ℕ → ℂ} {τ : ℝ}
    (hg : f =O[atTop] (fun n : ℕ => (n:ℝ)^τ)) {s : ℂ} (hs : τ+1<s.re) (q : ℕ) :
    LSeriesSummable (twistCoefficients f q) s := by
  rw [twist_eq]
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  exact (LSeries.abscissaOfAbsConv_le_of_isBigO_rpow
    (FinitenessRamanujanFourier.twisted_growth hg q)).trans_lt
    (by exact_mod_cast hs)

theorem local_disk_complex (a : ℕ → ℂ) (d : ℕ)
    (ha : ∀ p, p.Prime → ‖a p‖+1≤(p:ℝ)^d) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : (d:ℝ)<s.re) : (‖a p‖+1)*‖(p:ℂ)^(-s)‖<1 := by
  have H := FinitenessEulerDirichlet.local_disk a d ha hp hs
  simpa only [norm_natCast_cpow_of_pos hp.pos,neg_re,ofReal_re] using H

theorem product_at {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f) (s : ℂ)
    (hsum : ∀ q, LSeriesSummable (twistCoefficients f q) s)
    (hdisk : ∀ p, p.Prime → (‖(f p:ℂ)‖+1)*‖(p:ℂ)^(-s)‖<1) :
    ∀ q, q≠0 → LSeries (twistCoefficients f q) s=
      multiplier N f q s*LSeries f s := by
  apply Nat.recOnPrimePow
  · exact fun h => (h rfl).elim
  · intro _
    simp [twist_one,multiplier]
  · intro r p α hp hpr hα ih hq
    have hr : r≠0 := right_ne_zero_of_mul hq
    have hc : p.Coprime r := hp.coprime_iff_not_dvd.mpr hpr
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hα.ne'
    rw [prime_factor_step hf hp hc j s (hdisk p hp) (hsum r) (hsum _),
      ih hr,multiplier_mul (hc.pow_left (j+1)),multiplier_prime_pow hp]
    ring

/-- One right half-plane works simultaneously for EVERY positive q.
The formula uses actual original Euler inputs and literal Ramanujan twists. -/
theorem product_on_halfPlane {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f) :
    ∃ c : ℝ, ∀ s : ℂ, c<s.re → ∀ q, q≠0 →
      LSeries (twistCoefficients f q) s=
        multiplier N f q s*LSeries f s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  obtain ⟨d,hd⟩ := prime_bound (input_polynomial hf.zero hg)
  refine ⟨max (τ+1) (d:ℝ),fun s hs => ?_⟩
  apply product_at hf s
  · intro q
    exact twisted_summable hg (lt_of_le_of_lt (le_max_left _ _) hs) q
  · intro p hp
    exact local_disk_complex f d hd hp
      (lt_of_le_of_lt (le_max_right _ _) hs)

/-- The same formula in the original positive-index Dirichlet-series
definition, rather than only the library's LSeries wrapper. -/
theorem original_product {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f) :
    ∃ c : ℝ, ∀ s : ℂ, c<s.re → ∀ q, q≠0 →
      L (FinitenessRamanujanFourier.twisted f q) s=multiplier N f q s*L f s := by
  obtain ⟨c,hc⟩ := product_on_halfPlane hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨max c (τ+1),fun s hs q hq => ?_⟩
  have H := hc s (lt_of_le_of_lt (le_max_left _ _) hs) q hq
  have hs' : τ+1<s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have ht := twisted_summable hg hs' q
  have h1 := twisted_summable hg hs' 1
  rw [twist_one] at h1
  rw [twist_eq] at H ht
  rw [L_eq_mathlib (FinitenessRamanujanFourier.twisted_zero hf.zero q) ht,L_eq_mathlib hf.zero h1]
  exact H

#print axioms product_on_halfPlane
#print axioms original_product

end FinitenessTwistedEulerProduct
