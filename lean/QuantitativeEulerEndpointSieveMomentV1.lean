module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve

open Finset

/-- Total mass of the actual finite squarefree-subset Euler product. -/
theorem powerset_mass {ι : Type*} (S : Finset ι) (g : ι → ℝ) :
    (∑ T ∈ S.powerset, ∏ p ∈ T, g p)=∏ p ∈ S, (1+g p) := by
  classical
  simpa only [prod_const_one,mul_one,add_comm] using
    (Finset.prod_add g (fun _ => (1 : ℝ)) S).symm

/-- Exact first moment, with no independence hypothesis: all subset weights
are the explicitly expanded product. -/
theorem powerset_moment {ι : Type*} (S : Finset ι) (g c : ι → ℝ)
    (hg : ∀ p∈S, 0≤g p) :
    (∑ T ∈ S.powerset, (∏ p ∈ T, g p)*(∑ p ∈ T, c p))=
      (∏ p ∈ S, (1+g p))*(∑ p ∈ S, g p/(1+g p)*c p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hgS : ∀ p∈S, 0≤g p := fun p hp => hg p (mem_insert_of_mem hp)
    have hga : 1+g a≠0 := by have := hg a (mem_insert_self _ _); linarith
    rw [sum_powerset_insert ha]
    have hi : (∑ T ∈ S.powerset,
        (∏ p ∈ insert a T, g p)*(∑ p ∈ insert a T, c p))=
        g a*c a*(∑ T ∈ S.powerset, ∏ p ∈ T, g p)+
        g a*(∑ T ∈ S.powerset, (∏ p ∈ T, g p)*(∑ p ∈ T, c p)) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro T hT
      have haT : a∉T := fun hh => ha ((mem_powerset.mp hT) hh)
      rw [prod_insert haT,sum_insert haT]
      ring
    rw [hi,ih hgS,powerset_mass,prod_insert ha,sum_insert ha]
    field_simp
    ring

/-- Removing subsets whose total cost exceeds Z loses at most their first
moment divided by Z. The conclusion is the lower bound needed for a
truncated Selberg denominator. -/
theorem powerset_truncated_mass {ι : Type*} (S : Finset ι) (g c : ι → ℝ)
    (hg : ∀ p∈S, 0≤g p) (hc : ∀ p∈S, 0≤c p) {Z : ℝ} (hZ : 0<Z)
    (hmoment : (∑ p ∈ S, g p/(1+g p)*c p)≤Z/2) :
    (∏ p ∈ S, (1+g p))/2 ≤
      ∑ T ∈ S.powerset, if (∑ p ∈ T, c p)≤Z then ∏ p ∈ T, g p else 0 := by
  classical
  let mass : Finset ι → ℝ := fun T => ∏ p ∈ T, g p
  let cost : Finset ι → ℝ := fun T => ∑ p ∈ T, c p
  have hm (T : Finset ι) (hT : T∈S.powerset) : 0≤mass T :=
    prod_nonneg (fun p hp => hg p ((mem_powerset.mp hT) hp))
  have hcost (T : Finset ι) (hT : T∈S.powerset) : 0≤cost T :=
    sum_nonneg (fun p hp => hc p ((mem_powerset.mp hT) hp))
  have htail : Z*(∑ T ∈ S.powerset, if cost T≤Z then 0 else mass T) ≤
      ∑ T ∈ S.powerset, mass T*cost T := by
    rw [mul_sum]
    apply sum_le_sum
    intro T hT
    split_ifs with hh
    · simpa using mul_nonneg (hm T hT) (hcost T hT)
    · have hle : Z≤cost T := le_of_lt (lt_of_not_ge hh)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hle (hm T hT)
  have hsplit : (∑ T ∈ S.powerset, if cost T≤Z then mass T else 0)+
      (∑ T ∈ S.powerset, if cost T≤Z then 0 else mass T)=
        ∏ p ∈ S, (1+g p) := by
    rw [← sum_add_distrib,← powerset_mass S g]
    apply sum_congr rfl
    intro T _
    split_ifs <;> simp [mass]
  have hmom := powerset_moment S g c hg
  have hF : 0≤∏ p ∈ S, (1+g p) :=
    prod_nonneg (fun p hp => by linarith [hg p hp])
  have hbound := mul_le_mul_of_nonneg_left hmoment hF
  change (∑ T ∈ S.powerset, mass T*cost T)=_ at hmom
  rw [hmom] at htail
  change (∏ p ∈ S, (1+g p))/2 ≤
    ∑ T ∈ S.powerset, if cost T≤Z then mass T else 0
  nlinarith

/-- Specialization to the actual product of positive integers. The local
first-moment input is explicit; no logarithmic denominator growth is
assumed in this finite combinatorial estimate. -/
theorem truncated_squarefree_product_mass (S : Finset ℕ) (g : ℕ → ℝ)
    (hp : ∀ p∈S, 1≤p) (hg : ∀ p∈S, 0≤g p) {z : ℝ} (hz : 1<z)
    (hmoment : (∑ p ∈ S, g p/(1+g p)*Real.log p)≤Real.log z/2) :
    (∏ p ∈ S, (1+g p))/2 ≤
      ∑ T ∈ S.powerset,
        if (∏ p ∈ T, (p : ℝ))≤z then ∏ p ∈ T, g p else 0 := by
  classical
  have h := powerset_truncated_mass S g (fun p => Real.log p) hg
    (fun p h => Real.log_nonneg (by exact_mod_cast hp p h)) (Real.log_pos hz) hmoment
  convert h using 1
  apply sum_congr rfl
  intro T hT
  have hpT (p : ℕ) (hh : p∈T) : 0<(p : ℝ) := by
    exact_mod_cast (show 0<p from lt_of_lt_of_le Nat.zero_lt_one (hp p ((mem_powerset.mp hT) hh)))
  have hprod : 0<∏ p ∈ T, (p : ℝ) := prod_pos hpT
  have he : Real.log (∏ p ∈ T, (p : ℝ))=∑ p ∈ T, Real.log p :=
    Real.log_prod (fun p hh => (hpT p hh).ne')
  simp only [← he,Real.log_le_log_iff hprod (by linarith : 0<z)]

#print axioms powerset_moment
#print axioms powerset_truncated_mass
#print axioms truncated_squarefree_product_mass

end QuantitativeEulerEndpointSieve
