module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

namespace AsymptoticSectorComparison

open Filter Asymptotics
open scoped BigOperators

/-- The weight tends to infinity through the even integers. -/
def evenWeights : Filter ℕ := atTop ⊓ Filter.principal {k | Even k}

instance evenWeights_neBot : evenWeights.NeBot := by
  apply Filter.frequently_iff_neBot.mp
  rw [Filter.frequently_atTop]
  intro n
  exact ⟨n+n, by omega, ⟨n,rfl⟩⟩

/-- The epsilon formulation of a sector's asymptotic upper bound. -/
def LinearUpper (v : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ k in evenWeights, v k ≤ (c+ε)*(k:ℝ)

/-- Finitely many sector upper bounds can be added before making any
comparison with classical dimensions. No sector dimension formula is used. -/
theorem sum_upper {ι : Type*} [Fintype ι] (v : ι → ℕ → ℝ) (c : ι → ℝ)
    (h : ∀ i, LinearUpper (v i) (c i)) :
    LinearUpper (fun k => ∑ i, v i k) (∑ i, c i) := by
  classical
  intro ε hε
  let r : ℝ := ε/((Fintype.card ι:ℝ)+1)
  have hr : 0<r := by dsimp [r]; positivity
  have hsmall : (Fintype.card ι:ℝ)*r ≤ ε := by
    dsimp [r]
    have hd : (0:ℝ)<(Fintype.card ι:ℝ)+1 := by positivity
    have he := (div_mul_cancel₀ ε hd.ne')
    nlinarith [div_pos hε hd]
  filter_upwards [Filter.eventually_all.mpr (fun i => h i r hr)] with k hk
  calc
    ∑ i, v i k ≤ ∑ i, (c i+r)*(k:ℝ) := Finset.sum_le_sum (fun i _ => hk i)
    _ = ((∑ i, c i)+(Fintype.card ι:ℝ)*r)*(k:ℝ) := by
      simp only [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((∑ i, c i)+ε)*(k:ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg k)

/-- Squeeze the total count between the total classical dimension and the
sum of sector bounds. The only classical asymptotic input is for the TOTAL
dimension. This is the final reduction, not a proof of its analytic inputs. -/
theorem count_from_total_dimension {ι : Type*} [Fintype ι]
    (count dimension : ℕ → ℝ) (v : ι → ℕ → ℝ) (c : ι → ℝ)
    (hsector : ∀ i, LinearUpper (v i) (c i))
    (hlower : ∀ᶠ k in evenWeights, dimension k ≤ count k)
    (hupper : ∀ᶠ k in evenWeights, count k ≤ ∑ i, v i k)
    (hdimension : (fun k => dimension k-(∑ i, c i)*(k:ℝ))
      =o[evenWeights] (fun k => (k:ℝ))) :
    (fun k => count k-dimension k) =o[evenWeights] (fun k => (k:ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hhalf : 0<ε/2 := by linarith
  filter_upwards [hlower, hupper, sum_upper v c hsector (ε/2) hhalf,
    hdimension.bound hhalf] with k hlo hup hsum hdim
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have herror := (le_abs_self (-(dimension k-(∑ i, c i)*(k:ℝ)))).trans
    (by simpa only [abs_neg, Real.norm_eq_abs, abs_of_nonneg hk] using hdim)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlo),
    abs_of_nonneg hk] using (show count k-dimension k ≤ ε*(k:ℝ) by nlinarith)

/-- Summing all local sign traces removes every reversal term, including
the asymmetric sign contribution at conductor exponent two. -/
theorem sum_sign_traces {ι : Type*} [Fintype ι] [DecidableEq ι] (ν ρ : ι → ℝ) :
    (∑ σ : ι → Bool, ∏ i, (ν i + if σ i then ρ i else -ρ i)/2) = ∏ i, ν i := by
  classical
  rw [← Fintype.prod_sum (fun i (b : Bool) => (ν i + if b then ρ i else -ρ i)/2)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Group local Atkin--Lehner sign choices by their observed Euler sector
(Fricke sign and the signs at primes dividing N exactly once). Every local
sign choice is counted once, even when some observed sectors are empty. -/
theorem sum_grouped_sign_traces {ι J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] (sector : (ι → Bool) → J) (ν ρ : ι → ℝ) :
    (∑ j : J, (∑ σ : ι → Bool,
      if sector σ = j then ∏ i, (ν i + if σ i then ρ i else -ρ i)/2 else 0)/12) =
      (∏ i, ν i)/12 := by
  classical
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [sum_sign_traces]

#print axioms count_from_total_dimension
#print axioms sum_sign_traces
#print axioms sum_grouped_sign_traces

end AsymptoticSectorComparison
