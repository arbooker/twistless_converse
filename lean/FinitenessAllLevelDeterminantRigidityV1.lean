module

public import FinitenessAllLevelDeterminantPolynomialV1
public import FinitenessAllLevelPolynomialGrowthOrderV1
public import FinitenessAllLevelFiberProductBoundsV1
public import FinitenessAllLevelPrimeRigidityV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter Polynomial Bornology
open scoped Topology

/-- Two-prime rigidity by the determinant polynomial. The contradiction
uses integer polynomial degree and finite fiber degree; no end at infinity,
Puiseux parametrization, or analytic normalization is assumed. -/
theorem no_surjective_two_prime_family {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (R : ℂ → X → Prop)
    (hproper : IsProperMap (fun t : {t : ℂ × X | R t.1 t.2} => t.val.1))
    (hf : ∀ w, {x | R w x}.Finite) (hreg : regularValues R ∈ codiscrete ℂ)
    (b : X →L[ℂ] ℂ) {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    (hbounds : ∀ j : ℕ, ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ z x, R z x →
      (‖b x‖ ^ j ≤ C * (1 + ‖z‖) ^ Nat.ceil ((j : ℝ) * (Real.log r / Real.log p))) ∧
      (‖z‖ ^ j ≤ E * (1 + ‖b x‖) ^ Nat.ceil ((j : ℝ) * (Real.log p / Real.log r)))) :
    ¬ ∀ z, ∃ x, R z x := by
  classical
  intro hsurj
  obtain ⟨C₀, E₀, hC₀, hE₀, hfirst⟩ := hbounds 1
  have hbfirst (z : ℂ) (x : X) (hx : R z x) :
      ‖b x‖ ≤ max C₀ 1 * (1 + ‖z‖) ^ Nat.ceil (Real.log r / Real.log p) := by
    have hh := (hfirst z x hx).1
    simp only [pow_one, Nat.cast_one, one_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨D, P, hD, hprod⟩ := determinant_polynomial R hproper hf hreg b
    (le_max_right C₀ 1) (Nat.ceil (Real.log r / Real.log p)) hbfirst
  obtain ⟨z, hzg, hz⟩ := codiscrete_escaping_sequence hreg
  have hDpos : 0 < D := by
    obtain ⟨x, hx⟩ := hsurj (z 0)
    have hh : 0 < Nat.card {x | R (z 0) x} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨x, hx⟩⟩, (hf (z 0)).to_subtype⟩
    rwa [hD (z 0) (hzg 0)] at hh
  have hforward (j : ℕ) : j * P.natDegree ≤
      Nat.ceil ((j : ℝ) * (Real.log r / Real.log p)) * D := by
    obtain ⟨C, E, hC, _, hb⟩ := hbounds j
    apply polynomial_power_degree_bound z hz P j _ (pow_nonneg hC D)
    apply Eventually.of_forall
    intro t
    let := (hf (z t)).fintype
    have hcard : Fintype.card {x | R (z t) x} = D := by
      rw [← Nat.card_eq_fintype_card]
      exact hD (z t) (hzg t)
    rw [hprod (z t) (hzg t), finprod_eq_prod_of_fintype]
    have hh := fiber_product_forward (fun x : {x | R (z t) x} => ‖b x.val‖)
      (fun x => norm_nonneg _) ‖z t‖ C j
      (Nat.ceil ((j : ℝ) * (Real.log r / Real.log p)))
      (fun x => (hb (z t) x.val x.property).1)
    simpa only [hcard] using hh
  have hlarge : ∀ᶠ t in atTop, E₀ * 2 ^ Nat.ceil (Real.log p / Real.log r) < ‖z t‖ :=
    (tendsto_norm_atTop_iff_cobounded.mpr hz).eventually (eventually_gt_atTop _)
  have hreverse (j : ℕ) : j * D ≤
      Nat.ceil ((j : ℝ) * (Real.log p / Real.log r)) * P.natDegree := by
    obtain ⟨C, E, _, hE, hb⟩ := hbounds j
    apply base_power_degree_bound z hz P (j * D)
      (Nat.ceil ((j : ℝ) * (Real.log p / Real.log r)))
      (E ^ D * 2 ^ (Nat.ceil ((j : ℝ) * (Real.log p / Real.log r)) * D))
    filter_upwards [hlarge] with t ht
    let := (hf (z t)).fintype
    have hcard : Fintype.card {x | R (z t) x} = D := by
      rw [← Nat.card_eq_fintype_card]
      exact hD (z t) (hzg t)
    have hbone (x : {x | R (z t) x}) : 1 ≤ ‖b x.val‖ := by
      apply observable_one_le (norm_nonneg _) hE₀ (Nat.ceil (Real.log p / Real.log r)) ?_ ht
      simpa only [pow_one, Nat.cast_one, one_mul] using (hfirst (z t) x.val x.property).2
    rw [hprod (z t) (hzg t), finprod_eq_prod_of_fintype]
    have hh := fiber_product_reverse (fun x : {x | R (z t) x} => ‖b x.val‖)
      hbone (norm_nonneg (z t)) hE j
      (Nat.ceil ((j : ℝ) * (Real.log p / Real.log r)))
      (fun x => (hb (z t) x.val x.property).2)
    simpa only [hcard] using hh
  have hdeg : 0 < P.natDegree := by
    have hh := hreverse 1
    by_contra! hn
    have hn0 : P.natDegree = 0 := Nat.eq_zero_of_le_zero hn
    rw [hn0, mul_zero, one_mul] at hh
    omega
  exact FinitenessAllLevelPrimeRigidity.no_positive_pole_orders hr hp hne.symm hDpos hdeg
    (fun j _ => by exact_mod_cast hforward j) (fun j _ => by exact_mod_cast hreverse j)

#print axioms no_surjective_two_prime_family

end FinitenessAllLevelPolynomialPresentation
