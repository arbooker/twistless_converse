module

public import FinitenessNormalizedTwistLocalV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessNormalizedTwistProduct

open Complex FinitenessOriginalInput FinitenessTwistConductor FinitenessTwistExponential
  FinitenessNormalizedTwistLocal FinitenessTwistedEulerProduct

noncomputable def root (N : ℕ) (f : ℕ → ℂ) (q : ℕ) : ℂ :=
  ∏ p ∈ q.primeFactors, sign N f p (q.factorization p)

noncomputable def product (N : ℕ) (f : ℕ → ℂ) (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, factor N f p (q.factorization p) s

theorem root_unit {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f) (q : ℕ) :
    root N f q=1 ∨ root N f q= -1 := by
  have hs : (root N f q)^2=1 := by
    unfold root
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro p hp
    rcases sign_unit hf (Nat.prime_of_mem_primeFactors hp) (q.factorization p) with h|h <;>
      rw [h] <;> norm_num
  exact sq_eq_one_iff.mp hs

theorem reciprocal {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    (hN : 0<N) (q : ℕ) (s : ℂ) :
    product N f q s=(root N f q:ℂ)*product N f q (1-s) := by
  unfold product root
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun p hp =>
    FinitenessNormalizedTwistLocal.reciprocal hf hN
      (Nat.prime_of_mem_primeFactors hp) _ s)

theorem product_entire (N : ℕ) (f : ℕ → ℂ) (q : ℕ) :
    Differentiable ℂ (product N f q) := by
  apply Differentiable.fun_finsetProd
  intro p _
  exact factor_entire N f p _

theorem product_bound (N : ℕ) (f : ℕ → ℂ) (q : ℕ) :
    FinitenessFiniteOrder.Bound (product N f q) :=
  FinitenessFiniteOrderClosure.prod q.primeFactors _ (fun p _ => factor_bound N f p _)

theorem nat_prod_cpow {ι : Type*} (t : Finset ι) (v : ι → ℕ) (s : ℂ) :
    ((∏ i∈t,v i:ℕ):ℂ)^s=∏ i∈t,(v i:ℂ)^s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi,Finset.prod_insert hi,Nat.cast_mul,
        natCast_mul_natCast_cpow,ih]

theorem scale_as_cpow {p : ℕ} (hp : 0<p) (β : ℕ) (s : ℂ) :
    scale p β s=((p^β:ℕ):ℂ)^((s-1/2)/2) := by
  unfold scale
  rw [power_eq hp,Nat.cast_pow,← natCast_cpow_natCast_mul]
  congr 1
  ring

theorem scales_product {N q : ℕ} (hN : 0<N) (hq : 0<q) (s : ℂ) :
    (∏ p∈q.primeFactors,scale p (excess N p (q.factorization p)) s)=
      (ratio N q:ℂ)^((s-1/2)/2) := by
  rw [ratio_product hN hq,nat_prod_cpow]
  exact Finset.prod_congr rfl (fun p hp =>
    scale_as_cpow (Nat.prime_of_mem_primeFactors hp).pos _ s)

theorem factor_eq {N : ℕ} (f : ℕ → ℂ) {p : ℕ} (hp : 0<p) (α : ℕ) (s : ℂ) :
    factor N f p α s=scale p (excess N p α) s*localMultiplier N f s p α := by
  by_cases hα : α=0
  · simp [factor,localMultiplier,hα,excess,scale,power]
  · simp only [factor,localMultiplier,ite_eq_right hα,power_eq hp]

/-- Exact identification with the completed conductor correction. -/
theorem product_eq {N q : ℕ} (hN : 0<N) (hq : 0<q) (f : ℕ → ℂ) (s : ℂ) :
    product N f q s=(ratio N q:ℂ)^((s-1/2)/2)*multiplier N f q s := by
  unfold product
  have he := Finset.prod_congr (s₁:=q.primeFactors) rfl
    (fun p hp => factor_eq (N:=N) f (Nat.prime_of_mem_primeFactors hp).pos (q.factorization p) s)
  rw [he,Finset.prod_mul_distrib,scales_product hN hq]
  rfl

theorem completed_identity {N q k : ℕ} {f : ℕ → ℂ} (hN : 0<N) (hq : 0<q)
    (s : ℂ) (hL : L (FinitenessRamanujanFourier.twisted f q) s=multiplier N f q s*L f s) :
    completed (Nat.lcm N (q^2)) k (FinitenessRamanujanFourier.twisted f q) s=
      product N f q s*completed N k f s := by
  rw [product_eq hN hq]
  unfold completed
  rw [hL,← mul_ratio N q,Nat.cast_mul,natCast_mul_natCast_cpow]
  ring

#print axioms reciprocal
#print axioms product_entire
#print axioms product_bound
#print axioms completed_identity

end FinitenessNormalizedTwistProduct
