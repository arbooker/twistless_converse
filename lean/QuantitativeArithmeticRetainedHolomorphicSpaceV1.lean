module

public import QuantitativeArithmeticRetainedCutoffV1
public import QuantitativeArithmeticAugmentedSpanningV1
public import FinitenessHolomorphicSpaceV1

@[expose] public section

namespace QuantitativeArithmeticRetainedHolomorphicSpace

open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
  QuantitativeArithmeticRetainedReconstruction FinitenessHolomorphicSpace
open Function.Periodic

def CompleteLaws (S : Finset ℕ) (b : ℕ → ℂ) (F : ℂ → ℂ) : Prop :=
  ∀ p ∈ S, ∀ z : ℂ, 0 < z.im → completeTwist F p z = b p*F ((p : ℂ)*z)

theorem complete_add (F G : ℂ → ℂ) (p : ℕ) (z : ℂ) :
    completeTwist (F+G) p z = completeTwist F p z + completeTwist G p z := by
  simp only [completeTwist, Pi.add_apply, Finset.sum_add_distrib]

theorem complete_smul (a : ℂ) (F : ℂ → ℂ) (p : ℕ) (z : ℂ) :
    completeTwist (a • F) p z = a*completeTwist F p z := by
  simp only [completeTwist, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The old Ramanujan-law space with the actual retained complete-trace
laws. No growth or finite-dimensionality hypothesis is included. -/
def space (N Q : ℕ) (S : Finset ℕ) (χ b : ℕ → ℂ) (m : ℕ) :
    Submodule ℂ FinitenessDiskJet.space where
  carrier := {G | G ∈ FinitenessHolomorphicSpace.space N Q χ m ∧ CompleteLaws S b (lift G.val)}
  zero_mem' := by
    refine ⟨Submodule.zero_mem _,?_⟩
    intro p _ z _
    simp [completeTwist, FinitenessHolomorphicSpace.lift]
  add_mem' := by
    rintro F G ⟨hF,hFl⟩ ⟨hG,hGl⟩
    refine ⟨Submodule.add_mem _ hF hG,?_⟩
    intro p hp z hz
    change completeTwist (lift F.val + lift G.val) p z = _
    rw [complete_add,hFl p hp z hz,hGl p hp z hz]
    change _ = b p*(lift F.val ((p : ℂ)*z)+lift G.val ((p : ℂ)*z))
    ring
  smul_mem' := by
    rintro a G ⟨hG,hGl⟩
    refine ⟨Submodule.smul_mem _ a hG,?_⟩
    intro p hp z hz
    change completeTwist (a • lift G.val) p z = _
    rw [complete_smul,hGl p hp z hz]
    change _ = b p*(a*lift G.val ((p : ℂ)*z))
    ring

theorem dimension_bound {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N S Q hQ) (P : Parameters A)
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ∣ Q)
    (χ b : ℕ → ℂ) (m n : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) (hb : ∀ p ∈ S, ‖b p‖ ≤ (p : ℝ)^m)
    (hn : ((m+P.s : ℕ) : ℝ)+1 ≤ Real.pi*(n : ℝ)*P.ε) :
    FiniteDimensional ℂ (space N Q S χ b m) ∧
      Module.finrank ℂ (space N Q S χ b m) ≤ n := by
  apply FinitenessDiskJet.dimension_bound
  intro G hzero
  obtain ⟨⟨hG0,hGo,hGp,hGl⟩,hGc⟩ := G.property
  have hFzero := QuantitativeArithmeticRetainedCutoff.zero_of_jet hN A P hprime hdiv
    (lift G.val.val) G.val.val hGp χ b m hχ hb hGl hGc G.val.property hG0
    (fun _ _ => rfl) n hn hzero
  apply Subtype.ext
  apply Subtype.ext
  funext w
  change G.val.val w = 0
  by_cases hw0 : w = 0
  · exact hw0 ▸ hG0
  by_cases hwo : 1 ≤ ‖w‖
  · exact hGo w hwo
  have hw : ‖w‖ < 1 := lt_of_not_ge hwo
  have hz : 0 < (invQParam 1 w).im := by
    rw [im_invQParam]
    exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by norm_num) (by positivity))
      (Real.log_neg (norm_pos_iff.mpr hw0) hw)
  have hh := hFzero (invQParam 1 w) hz
  simpa only [FinitenessHolomorphicSpace.lift, qParam_right_inv (by norm_num : (1 : ℝ) ≠ 0) hw0] using hh

/-- A uniform O(k) bound for each fixed set of complete-trace multipliers. -/
theorem linear_bound {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N S Q hQ) (P : Parameters A)
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ∣ Q) :
    ∃ C : ℕ, 0 < C ∧ ∀ (χ b : ℕ → ℂ) (m : ℕ), 0 < m →
      (∀ q, q ∣ Q → ‖χ q‖ = 1) → (∀ p ∈ S, ‖b p‖ ≤ (p : ℝ)^m) →
      FiniteDimensional ℂ (space N Q S χ b m) ∧
        Module.finrank ℂ (space N Q S χ b m) ≤ C*m := by
  obtain ⟨D,hD⟩ := exists_nat_gt (1/(Real.pi*P.ε))
  have hpe : 0 < Real.pi*P.ε := mul_pos Real.pi_pos P.epsilon_pos
  have hD0 : 0 < D := by exact_mod_cast ((div_pos (by norm_num) hpe).trans hD)
  have hD1 : 1 ≤ Real.pi*(D : ℝ)*P.ε := by
    have := (div_lt_iff₀ hpe).mp hD
    nlinarith
  refine ⟨D*(P.s+2), Nat.mul_pos hD0 (by omega), ?_⟩
  intro χ b m hm hχ hb
  have hn : ((m+P.s : ℕ) : ℝ)+1 ≤ Real.pi*((D*(m+P.s+1) : ℕ) : ℝ)*P.ε := by
    have hh := mul_le_mul_of_nonneg_right hD1 (show 0 ≤ ((m+P.s+1 : ℕ) : ℝ) by positivity)
    push_cast at hh ⊢
    nlinarith
  obtain ⟨hfd,hfin⟩ := dimension_bound hN A P hprime hdiv χ b m (D*(m+P.s+1)) hχ hb hn
  refine ⟨hfd,hfin.trans ?_⟩
  calc
    D*(m+P.s+1) ≤ D*((P.s+2)*m) := Nat.mul_le_mul_left D (by nlinarith)
    _ = (D*(P.s+2))*m := by ring

/-- In the radical range the full mixed holomorphic space has a linear
dimension bound, uniformly in weight and in all bounded multipliers. -/
theorem radical_level (N : ℕ) (hN : 0 < N)
    (hrad : N < (∏ p ∈ N.primeFactors, p)^2) :
    ∃ Q C : ℕ, 0 < Q ∧ N ∣ Q ∧ 0 < C ∧ ∀ (χ b : ℕ → ℂ) (m : ℕ),
      0 < m → (∀ q, q ∣ Q → ‖χ q‖ = 1) →
      (∀ p ∈ N.primeFactors, ‖b p‖ ≤ (p : ℝ)^m) →
      FiniteDimensional ℂ (space N Q N.primeFactors χ b m) ∧
        Module.finrank ℂ (space N Q N.primeFactors χ b m) ≤ C*m := by
  obtain ⟨Q,hQ,hNQ,⟨A⟩⟩ := QuantitativeArithmeticAugmentedSpanning.radical_certificate hN hrad
  obtain ⟨P⟩ := parameters_exist hN hQ A
  obtain ⟨C,hC,hh⟩ := linear_bound hN A P
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun _ hp => (Nat.dvd_of_mem_primeFactors hp).trans hNQ)
  exact ⟨Q,C,hQ,hNQ,hC,hh⟩

#print axioms dimension_bound
#print axioms linear_bound
#print axioms radical_level

end QuantitativeArithmeticRetainedHolomorphicSpace
