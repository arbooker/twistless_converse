module

public import FinitenessAllLevelSectorAtlasV1
public import FinitenessAllLevelUniformTwoPrimeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelAnalyticAtlas

open Complex Set FinitenessAllLevelAnalyticSubstitution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {I : Type*} {R : ℂ → X → Prop}

/-- Every bounded linear coefficient on the ambient Banach space is
holomorphic on every chart of the actual zero-set atlas. -/
theorem Chart.linear_coordinate_analytic (c : Chart I R) (l : X →L[ℂ] ℂ) :
    AnalyticOnNhd ℂ (fun t : ℂ × c.E => l (c.lift t.1 t.2)) (c.U ×ˢ univ) :=
  fun t ht => (l.analyticAt _).comp (joint_analytic c.analytic_lift t ht)

/-- Coefficient expressions agree across the exact chart transitions. -/
theorem Chart.linear_coordinate_transition (c d : Chart I R) (l : X →L[ℂ] ℂ)
    {z : ℂ} (hc : z ∈ c.U) (hd : z ∈ d.U) (v : c.E) (hv : c.equations (z, v) = 0) :
    l (d.lift z (c.transition d (z, v)).2) = l (c.lift z v) :=
  congrArg l (c.transition_exact d hc hd v hv).2

#print axioms Chart.linear_coordinate_analytic
#print axioms Chart.linear_coordinate_transition

end FinitenessAllLevelAnalyticAtlas

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelGlobalHeight FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelFormalContinuation
  FinitenessAllLevelCoefficientFunctional FinitenessOriginalInput
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- All coefficient coordinates on an exact sector point are simultaneously
those of one literal original solution; the first coordinate is its retained
prime coefficient. This holds globally without an eigenvalue bound. -/
theorem global_sector_coefficients (hN : 0 < N) (hp : p.Prime) (hpQ : p ∣ Q)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool)
    (t : sectorLocus hN A P hb hba m s) :
    ∃ f : S N (2 * m), f.val p = t.val.1 ∧
      ∀ n, normalizedCLM (radius_pos a) (2 * m) n t.val.2 = f.val n := by
  obtain ⟨f, he, hF⟩ := constraints_recover_global hN hp hpQ hm A P (hb.trans hba) hae
    (sector Q m s) t.val.1 t.val.2 (fun q _ => sector_norm Q m s q)
    (sector_signs Q m s 1) t.property.2
  refine ⟨f, he, fun n => ?_⟩
  rw [← hF]
  exact normalized_representative (radius_pos a) (radius_lt_one (hb.trans hba)) f n

/-- The sharp two-prime growth bounds hold on the entire exact sector, for
its actual globally defined holomorphic coefficient coordinates. -/
theorem global_sector_two_prime_bounds {r : ℕ}
    (hN : 0 < N) (hp : p.Prime) (hpgood : ¬ p ∣ N) (hplarge : N < p ^ 2)
    (hr : r.Prime) (hrgood : ¬ r ∣ N) (hrlarge : N < r ^ 2) (hpQ : p ∣ Q)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (j : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ s : Fin (Q + 1) → Bool,
      ∀ t : sectorLocus hN A P hb hba m s,
        (‖normalizedCLM (radius_pos a) (2 * m) r t.val.2‖ ^ j ≤
          C * (1 + ‖t.val.1‖) ^ Nat.ceil ((j : ℝ) * (Real.log r / Real.log p))) ∧
        (‖t.val.1‖ ^ j ≤ D * (1 + ‖normalizedCLM (radius_pos a) (2 * m) r t.val.2‖) ^
          Nat.ceil ((j : ℝ) * (Real.log p / Real.log r))) := by
  obtain ⟨C, hC, hc⟩ := FinitenessAllLevelTwoPrimeBounds.original_ceiling_comparison
    hN hp hpgood hplarge hr hrgood m j
  obtain ⟨D, hD, hd⟩ := FinitenessAllLevelTwoPrimeBounds.original_ceiling_comparison
    hN hr hrgood hrlarge hp hpgood m j
  refine ⟨C, D, hC, hD, fun s t => ?_⟩
  obtain ⟨f, he, hcoeff⟩ := global_sector_coefficients hN hp hpQ A P hb hba hae hm s t
  rw [hcoeff r, ← he]
  exact ⟨hc f, hd f⟩

#print axioms global_sector_coefficients
#print axioms global_sector_two_prime_bounds

end FinitenessAllLevelConstraintLocus
