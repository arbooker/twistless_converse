module

public import FinitenessLowHeightV1
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

namespace FinitenessGlobalHeight

open FinitenessCertificate FinitenessIntegerWeight FinitenessComplexGeometry
open FinitenessAnalyticReconstruction SpanningIntegerRows

structure Parameters {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ) where
  ε : ℝ
  ρ : ℝ
  s : ℕ
  epsilon_pos : 0 < ε
  rho_pos : 0 < ρ
  rho_lt_one : ρ < 1
  mass_bound : cost A * ρ^s ≤ 1
  small : ∀ j : Fin Q, ∀ i ∈ (A.coeff j).support, ∀ z : ℂ,
    (j : ℝ)/Q ≤ z.re → z.re ≤ ((j : ℝ)+1)/Q → 0 ≤ z.im → z.im ≤ ε →
    denominator (Nat.lcm N (i.val.1^2)) (z + ((i.val.2 : ℂ)-(j : ℕ))/Q) ≤ ρ

theorem parameters_exist {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (A : Certificate N Q hQ) : Nonempty (Parameters A) := by
  obtain ⟨ε, ρ, he, hr, hr1, hb⟩ := FinitenessWindowGain.certificate_gain hN hQ A
  obtain ⟨s, hs⟩ := exists_exponent ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_cost A)) hr1
  refine ⟨⟨ε, ρ, s, he, hr, hr1, hs, ?_⟩⟩
  intro j i hi z hxlo hxhi hy hye
  have hre : (z + ((i.val.2 : ℂ)-(j : ℕ))/Q).re =
      z.re + ((i.val.2 : ℝ)-(j : ℝ))/Q := by simp
  have him : (z + ((i.val.2 : ℂ)-(j : ℕ))/Q).im = z.im := by simp
  unfold denominator
  rw [hre, him]
  apply hb j i hi _ z.im _ _ hy hye
  · simp only [sub_div]
    linarith
  · simp only [sub_div, add_div] at *
    linarith

theorem cell_exists {Q : ℕ} (hQ : 0 < Q) {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    ∃ j : Fin Q, (j : ℝ)/Q ≤ x ∧ x ≤ ((j : ℝ)+1)/Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hprod : 0 ≤ (Q : ℝ)*x := mul_nonneg hQ'.le hx
  let j : ℕ := Nat.floor ((Q : ℝ)*x)
  have hj : j < Q := (Nat.floor_lt hprod).mpr (by nlinarith)
  refine ⟨⟨j,hj⟩, ?_, ?_⟩
  · exact (div_le_iff₀ hQ').mpr (by simpa [j, mul_comm] using Nat.floor_le hprod)
  · exact (le_div_iff₀ hQ').mpr (by simpa [j, mul_comm] using (Nat.lt_floor_add_one ((Q : ℝ)*x)).le)

theorem periodic_reduction (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (z : ℂ) :
    ∃ w : ℂ, 0 ≤ w.re ∧ w.re < 1 ∧ w.im = z.im ∧ F w = F z := by
  let n : ℤ := Int.floor z.re
  refine ⟨z - (n : ℂ), ?_, ?_, by simp, ?_⟩
  · simp [n]
  · change z.re - (n : ℝ) < 1
    exact Int.fract_lt_one z.re
  · have hp' : Function.Periodic F (1 : ℂ) := hp
    simpa using (hp'.zsmul n).sub_eq z

theorem pointwise {N Q : ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N Q hQ) (P : Parameters A)
    (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (χ : ℕ → ℂ) (m : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
      twist F q z = χ q / (((Real.sqrt (Nat.lcm N (q^2)) : ℝ) : ℂ) * z)^(2*m) *
        twist F q (-1 / ((Nat.lcm N (q^2) : ℕ) * z)))
    (z : ℂ) (hz : 0 < z.im) (hze : z.im ≤ P.ε) {M : ℝ} (hM : 0 ≤ M)
    (habove : ∀ w : ℂ, z.im/P.ρ ≤ w.im → w.im^(m+P.s) * ‖F w‖ ≤ M) :
    z.im^(m+P.s) * ‖F z‖ ≤ M := by
  obtain ⟨w, hw0, hw1, him, hv⟩ := periodic_reduction F hp z
  obtain ⟨j,hj0,hj1⟩ := cell_exists hQ hw0 hw1
  have hwp : 0 < w.im := by simpa only [him] using hz
  have hwe : w.im ≤ P.ε := by simpa only [him] using hze
  have h := FinitenessLowHeight.from_FE hN A F hp χ m P.s hχ hFE j w hwp
    P.rho_pos hM P.mass_bound
    (fun i hi => P.small j i hi w hj0 hj1 hwp.le hwe)
    (by simpa only [him] using habove)
  simpa only [him, hv] using h

#print axioms parameters_exist
#print axioms pointwise

end FinitenessGlobalHeight
