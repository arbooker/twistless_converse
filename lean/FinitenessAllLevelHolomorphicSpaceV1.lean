module

public import FinitenessAllLevelCutoffV1
public import FinitenessAllLevelAuxiliaryV1
public import FinitenessHolomorphicSpaceV1

@[expose] public section

namespace FinitenessAllLevelHolomorphicSpace

open QuantitativeArithmeticRetainedCertificate FinitenessAllLevelGlobalHeight
  QuantitativeArithmeticRetainedReconstruction FinitenessHolomorphicSpace
open Function.Periodic

def CompleteLaws (S : Finset ℕ) (lam : ℕ → ℂ) (m : ℕ) (F : ℂ → ℂ) : Prop :=
  ∀ p ∈ S, ∀ z : ℂ, 0 < z.im → completeTwist F p z =
    FinitenessAllLevelGoodTrace.firstMultiplier lam m p * F ((p : ℂ)*z) -
      (p : ℂ) ^ (2 * m) * F ((p : ℂ) ^ 2 * z)

theorem complete_add (F G : ℂ → ℂ) (p : ℕ) (z : ℂ) :
    completeTwist (F+G) p z = completeTwist F p z + completeTwist G p z := by
  simp only [completeTwist, Pi.add_apply, Finset.sum_add_distrib]

theorem complete_smul (a : ℂ) (F : ℂ → ℂ) (p : ℕ) (z : ℂ) :
    completeTwist (a • F) p z = a*completeTwist F p z := by
  simp only [completeTwist, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The old Ramanujan-law space with the actual two-dilation complete-trace
laws at good primes. No growth or finite-dimensionality hypothesis is included. -/
def space (N Q : ℕ) (S : Finset ℕ) (χ lam : ℕ → ℂ) (m : ℕ) :
    Submodule ℂ FinitenessDiskJet.space where
  carrier := {G | G ∈ FinitenessHolomorphicSpace.space N Q χ m ∧ CompleteLaws S lam m (lift G.val)}
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
    change _ = FinitenessAllLevelGoodTrace.firstMultiplier lam m p *
      (lift F.val ((p : ℂ)*z)+lift G.val ((p : ℂ)*z)) -
      (p : ℂ) ^ (2 * m) * (lift F.val ((p : ℂ)^2*z)+lift G.val ((p : ℂ)^2*z))
    ring
  smul_mem' := by
    rintro a G ⟨hG,hGl⟩
    refine ⟨Submodule.smul_mem _ a hG,?_⟩
    intro p hp z hz
    change completeTwist (a • lift G.val) p z = _
    rw [complete_smul,hGl p hp z hz]
    change _ = FinitenessAllLevelGoodTrace.firstMultiplier lam m p *
      (a*lift G.val ((p : ℂ)*z)) - (p : ℂ) ^ (2 * m) * (a*lift G.val ((p : ℂ)^2*z))
    ring

theorem dimension_bound {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N S Q hQ) {L : ℝ} (P : Parameters A L)
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ∣ Q)
    (χ lam : ℕ → ℂ) (m n : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) (hlam : ∀ p ∈ S, ‖lam p‖ ≤ L)
    (hn : ((m+P.s : ℕ) : ℝ)+1 ≤ Real.pi*(n : ℝ)*P.ε) :
    FiniteDimensional ℂ (space N Q S χ lam m) ∧
      Module.finrank ℂ (space N Q S χ lam m) ≤ n := by
  apply FinitenessDiskJet.dimension_bound
  intro G hzero
  obtain ⟨⟨hG0,hGo,hGp,hGl⟩,hGc⟩ := G.property
  have hFzero := FinitenessAllLevelCutoff.zero_of_jet hN A P hprime hdiv
    (lift G.val.val) G.val.val hGp χ lam m hχ hlam hGl hGc G.val.property hG0
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

/-- A uniform O(k) bound for each fixed set of good-prime eigenvalues, uniform on bounded sets. -/
theorem linear_bound {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N S Q hQ) {L : ℝ} (P : Parameters A L)
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ∣ Q) :
    ∃ C : ℕ, 0 < C ∧ ∀ (χ lam : ℕ → ℂ) (m : ℕ), 0 < m →
      (∀ q, q ∣ Q → ‖χ q‖ = 1) → (∀ p ∈ S, ‖lam p‖ ≤ L) →
      FiniteDimensional ℂ (space N Q S χ lam m) ∧
        Module.finrank ℂ (space N Q S χ lam m) ≤ C*m := by
  obtain ⟨D,hD⟩ := exists_nat_gt (1/(Real.pi*P.ε))
  have hpe : 0 < Real.pi*P.ε := mul_pos Real.pi_pos P.epsilon_pos
  have hD0 : 0 < D := by exact_mod_cast ((div_pos (by norm_num) hpe).trans hD)
  have hD1 : 1 ≤ Real.pi*(D : ℝ)*P.ε := by
    have := (div_lt_iff₀ hpe).mp hD
    nlinarith
  refine ⟨D*(P.s+2), Nat.mul_pos hD0 (by omega), ?_⟩
  intro χ lam m hm hχ hlam
  have hn : ((m+P.s : ℕ) : ℝ)+1 ≤ Real.pi*((D*(m+P.s+1) : ℕ) : ℝ)*P.ε := by
    have hh := mul_le_mul_of_nonneg_right hD1 (show 0 ≤ ((m+P.s+1 : ℕ) : ℝ) by positivity)
    push_cast at hh ⊢
    nlinarith
  obtain ⟨hfd,hfin⟩ := dimension_bound hN A P hprime hdiv χ lam m (D*(m+P.s+1)) hχ hlam hn
  refine ⟨hfd,hfin.trans ?_⟩
  calc
    D*(m+P.s+1) ≤ D*((P.s+2)*m) := Nat.mul_le_mul_left D (by nlinarith)
    _ = (D*(P.s+2))*m := by ring

/-- At every positive level, fixed good-prime eigenvalue spaces have a
linear weight bound, uniformly for the eigenvalue in a fixed bounded set.
No coefficient growth condition is included in these spaces. -/
theorem good_prime_level {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L) :
    ∃ Q C : ℕ, 0 < Q ∧ N ∣ Q ∧ p ∣ Q ∧ 0 < C ∧
      ∀ (χ lam : ℕ → ℂ) (m : ℕ), 0 < m →
      (∀ q, q ∣ Q → ‖χ q‖ = 1) → ‖lam p‖ ≤ L →
      FiniteDimensional ℂ (space N Q {p} χ lam m) ∧
        Module.finrank ℂ (space N Q {p} χ lam m) ≤ C * m := by
  obtain ⟨Q, hQ, hNQ, hpQ, ⟨A⟩⟩ :=
    FinitenessAllLevelAuxiliary.certificate_at_prime hN hp hlarge
  obtain ⟨P⟩ := parameters_exist hN hQ A hL
  obtain ⟨C, hC, hh⟩ := linear_bound hN A P
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hp)
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hpQ)
  refine ⟨Q, C, hQ, hNQ, hpQ, hC, fun χ lam m hm hχ hlam => ?_⟩
  apply hh χ lam m hm hχ
  intro q hq
  simpa only [Finset.mem_singleton.mp hq] using hlam

#print axioms dimension_bound
#print axioms linear_bound
#print axioms good_prime_level

end FinitenessAllLevelHolomorphicSpace

