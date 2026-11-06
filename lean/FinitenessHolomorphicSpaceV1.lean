module

public import FinitenessDiskJetV1
public import FinitenessHolomorphicCutoffV1

@[expose] public section

namespace FinitenessHolomorphicSpace

open FinitenessAnalyticReconstruction FinitenessCertificate FinitenessGlobalHeight
open Function.Periodic

noncomputable def lift (G : ℂ → ℂ) (z : ℂ) : ℂ := G (qParam 1 z)

def Laws (N Q : ℕ) (χ : ℕ → ℂ) (m : ℕ) (F : ℂ → ℂ) : Prop :=
  ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
    twist F q z = χ q / (((Real.sqrt (Nat.lcm N (q^2)) : ℝ) : ℂ)*z)^(2*m) *
      twist F q (-1/((Nat.lcm N (q^2) : ℕ)*z))

theorem twist_add (F G : ℂ → ℂ) (q : ℕ) (z : ℂ) :
    twist (F+G) q z = twist F q z + twist G q z := by
  simp only [twist, Pi.add_apply, Finset.sum_add_distrib]

theorem twist_smul (a : ℂ) (F : ℂ → ℂ) (q : ℕ) (z : ℂ) :
    twist (a • F) q z = a * twist F q z := by
  simp only [twist, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem laws_add {N Q m : ℕ} {χ : ℕ → ℂ} {F G : ℂ → ℂ}
    (hF : Laws N Q χ m F) (hG : Laws N Q χ m G) : Laws N Q χ m (F+G) := by
  intro q hq z hz
  rw [twist_add, hF q hq z hz, hG q hq z hz, twist_add, mul_add]

theorem laws_smul {N Q m : ℕ} {χ : ℕ → ℂ} {F : ℂ → ℂ}
    (hF : Laws N Q χ m F) (a : ℂ) : Laws N Q χ m (a • F) := by
  intro q hq z hz
  rw [twist_smul, hF q hq z hz, twist_smul]
  ring

/-- Canonical zero extension outside the disk removes irrelevant values.
Inside the disk these are precisely holomorphic cuspidal solutions of the
specified transformation laws. Periodicity is retained as an explicit law. -/
def space (N Q : ℕ) (χ : ℕ → ℂ) (m : ℕ) : Submodule ℂ FinitenessDiskJet.space where
  carrier := {G | G.val 0 = 0 ∧ (∀ w : ℂ, 1 ≤ ‖w‖ → G.val w = 0) ∧
    (∀ z : ℂ, lift G.val (z+1) = lift G.val z) ∧ Laws N Q χ m (lift G.val)}
  zero_mem' := by
    refine ⟨rfl, fun _ _ => rfl, fun _ => rfl, ?_⟩
    intro q _ z _
    simp [twist, lift]
  add_mem' := by
    rintro F G ⟨hF0,hFo,hFp,hFl⟩ ⟨hG0,hGo,hGp,hGl⟩
    refine ⟨by simpa using congrArg₂ (·+·) hF0 hG0, ?_, ?_, laws_add hFl hGl⟩
    · intro w hw
      change F.val w+G.val w=0
      rw [hFo w hw, hGo w hw, add_zero]
    · intro z
      change lift F.val (z+1)+lift G.val (z+1) = lift F.val z+lift G.val z
      rw [hFp, hGp]
  smul_mem' := by
    rintro a G ⟨hG0,hGo,hGp,hGl⟩
    refine ⟨?_, ?_, ?_, laws_smul hGl a⟩
    · change a*G.val 0=0
      rw [hG0,mul_zero]
    · intro w hw
      change a*G.val w=0
      rw [hGo w hw,mul_zero]
    · intro z
      change a*lift G.val (z+1)=a*lift G.val z
      rw [hGp]

theorem dimension_bound {N Q : ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N Q hQ) (P : Parameters A) (χ : ℕ → ℂ) (m n : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (hn : ((m+P.s : ℕ) : ℝ)+1 ≤ Real.pi*(n : ℝ)*P.ε) :
    FiniteDimensional ℂ (space N Q χ m) ∧ Module.finrank ℂ (space N Q χ m) ≤ n := by
  apply FinitenessDiskJet.dimension_bound
  intro G hzero
  obtain ⟨hG0,hGo,hGp,hGl⟩ := G.property
  have hFzero := FinitenessHolomorphicCutoff.zero_of_jet hN A P
    (lift G.val.val) G.val.val hGp χ m hχ hGl G.val.property hG0
    (fun _ _ => rfl) n hn hzero
  apply Subtype.ext
  apply Subtype.ext
  funext w
  change G.val.val w = 0
  by_cases hw0 : w=0
  · exact hw0 ▸ hG0
  by_cases hwo : 1 ≤ ‖w‖
  · exact hGo w hwo
  have hw : ‖w‖ < 1 := lt_of_not_ge hwo
  have hz : 0 < (invQParam 1 w).im := by
    rw [im_invQParam]
    exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by norm_num) (by positivity))
      (Real.log_neg (norm_pos_iff.mpr hw0) hw)
  have hh := hFzero (invQParam 1 w) hz
  simpa only [lift, qParam_right_inv (by norm_num : (1 : ℝ) ≠ 0) hw0] using hh

/-- Uniformity in the multiplier pattern and weight. A fixed finite set of
twist laws gives a dimension bound linear in m=k/2. -/
theorem linear_bound {N Q : ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N Q hQ) (P : Parameters A) :
    ∃ C : ℕ, 0 < C ∧ ∀ (χ : ℕ → ℂ) (m : ℕ), 0 < m →
      (∀ q, q ∣ Q → ‖χ q‖ = 1) →
      FiniteDimensional ℂ (space N Q χ m) ∧
        Module.finrank ℂ (space N Q χ m) ≤ C*m := by
  obtain ⟨D,hD⟩ := exists_nat_gt (1/(Real.pi*P.ε))
  have hpe : 0 < Real.pi*P.ε := mul_pos Real.pi_pos P.epsilon_pos
  have hD0 : 0 < D := by
    exact_mod_cast ((div_pos (by norm_num) hpe).trans hD)
  have hD1 : 1 ≤ Real.pi*(D : ℝ)*P.ε := by
    have := (div_lt_iff₀ hpe).mp hD
    nlinarith
  refine ⟨D*(P.s+2), Nat.mul_pos hD0 (by omega), ?_⟩
  intro χ m hm hχ
  have hn : ((m+P.s : ℕ) : ℝ)+1 ≤ Real.pi*((D*(m+P.s+1) : ℕ) : ℝ)*P.ε := by
    have hh := mul_le_mul_of_nonneg_right hD1
      (show 0 ≤ ((m+P.s+1 : ℕ) : ℝ) by positivity)
    push_cast at hh ⊢
    nlinarith
  obtain ⟨hfd,hfin⟩ := dimension_bound hN A P χ m (D*(m+P.s+1)) hχ hn
  refine ⟨hfd, hfin.trans ?_⟩
  calc
    D*(m+P.s+1) ≤ D*((P.s+2)*m) := Nat.mul_le_mul_left D (by nlinarith)
    _ = (D*(P.s+2))*m := by ring

/-- The completed spanning theorem supplies the certificate, so the
holomorphic fixed-multiplier finiteness theorem has only the original
arithmetic restrictions on N. It does NOT yet identify original L-series
solutions with these holomorphic functions. -/
theorem admissible_level (N : ℕ) (hN : 0 < N) (h16 : ¬16 ∣ N)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p^2 ∣ N) :
    ∃ Q C : ℕ, 0 < Q ∧ N ∣ Q ∧ 0 < C ∧ ∀ (χ : ℕ → ℂ) (m : ℕ),
      0 < m → (∀ q, q ∣ Q → ‖χ q‖ = 1) →
      FiniteDimensional ℂ (space N Q χ m) ∧
        Module.finrank ℂ (space N Q χ m) ≤ C*m := by
  obtain ⟨Q,hQ,hNQ,⟨A⟩⟩ := exists_certificate N hN h16 hsq
  obtain ⟨P⟩ := parameters_exist hN hQ A
  obtain ⟨C,hC,hh⟩ := linear_bound hN A P
  exact ⟨Q,C,hQ,hNQ,hC,hh⟩

#print axioms dimension_bound
#print axioms linear_bound
#print axioms admissible_level

end FinitenessHolomorphicSpace
