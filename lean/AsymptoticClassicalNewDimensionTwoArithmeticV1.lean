module

public import AsymptoticClassicalNewDimensionArithmeticV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace AsymptoticClassicalDimension
open AsymptoticCongruenceStrip AsymptoticTotalNewCorner

/-- An already ramified prime multiplies the congruence index by p. -/
theorem full_index_mul_ramified (M p : ℕ) (hM : 0 < M) (hp : 0 < p) (hpM : p ∣ M) :
    (gamma (p * M)).relIndex (gamma 1) = p * (gamma M).relIndex (gamma 1) := by
  have hh := Subgroup.relIndex_mul_relIndex (gamma (p * M)) (gamma M) (gamma 1)
    (gamma_le_of_dvd (Nat.dvd_mul_left M p)) (gamma_le_of_dvd (one_dvd M))
  rw [AsymptoticRamifiedCosets.projective_index M p hM hp hpM] at hh
  exact hh.symm

theorem fullLeading_mul_ramified (M p : ℕ) (hM : 0 < M) (hp : 0 < p) (hpM : p ∣ M) :
    fullLeading (p * M) = (p : ℝ) * fullLeading M := by
  rw [fullLeading, full_index_mul_ramified M p hM hp hpM, Nat.cast_mul]
  unfold fullLeading
  ring

/-- The repeated-2 second difference simplifies to the index four levels below. -/
theorem twoLeading_four_mul (L : ℕ) (hL : 0 < L) : twoLeading (4 * L) = fullLeading L := by
  unfold twoLeading fullLeading
  have hdiv2 : 4 * L / 2 = 2 * L := by omega
  have hdiv4 : 4 * L / 4 = L := Nat.mul_div_cancel_left L (by decide)
  rw [hdiv2, hdiv4, show 4 * L = 2 * (2 * L) by ring,
    full_index_mul_ramified (2 * L) 2 (by omega) (by decide) (Nat.dvd_mul_right 2 L), Nat.cast_mul]
  norm_num

/-- The repeated-2 leading coefficient has the same p+1 homogeneity at any new prime. -/
theorem twoLeading_mul_prime (M p : ℕ) (hM : 0 < M) (h4 : 4 ∣ M)
    (hp : p.Prime) (hpM : ¬ p ∣ M) :
    twoLeading (p * M) = ((p : ℝ) + 1) * twoLeading M := by
  obtain ⟨L, rfl⟩ := h4
  have hL : 0 < L := by omega
  have hpL : ¬ p ∣ L := fun h => hpM (dvd_mul_of_dvd_right h 4)
  rw [show p * (4 * L) = 4 * (p * L) by ring,
    twoLeading_four_mul (p * L) (Nat.mul_pos hp.pos hL), twoLeading_four_mul L hL,
    fullLeading_mul_prime L p hL hp hpL]

/-- The second-difference coefficient is exactly the arithmetic local new factor at 2. -/
theorem twoLeading_eq_localFactor (N : ℕ) (hN : 0 < N) (h4 : 4 ∣ N) :
    twoLeading N = fullLeading N * localFactor N 2 := by
  obtain ⟨L, rfl⟩ := h4
  have hL : 0 < L := by omega
  have h8 : 2^3 ∣ 4 * L ↔ 2 ∣ L := by
    rw [show 2^3 = 4 * 2 by decide]
    exact Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)
  have hfour : 2^2 ∣ 4 * L := by simp
  rw [twoLeading_four_mul L hL, localFactor, ite_eq_left hfour]
  have hleading : fullLeading (4 * L) = 2 * fullLeading (2 * L) := by
    rw [show 4 * L = 2 * (2 * L) by ring,
      fullLeading_mul_ramified (2 * L) 2 (by omega) (by decide) (Nat.dvd_mul_right 2 L)]
    norm_num
  rw [hleading]
  by_cases h2 : 2 ∣ L
  · rw [ite_eq_left (h8.mpr h2), fullLeading_mul_ramified L 2 hL (by decide) h2]
    norm_num
    ring
  · rw [ite_eq_right (fun h => h2 (h8.mp h)), fullLeading_mul_prime L 2 hL Nat.prime_two h2]
    norm_num
    ring

#print axioms full_index_mul_ramified
#print axioms fullLeading_mul_ramified
#print axioms twoLeading_four_mul
#print axioms twoLeading_mul_prime
#print axioms twoLeading_eq_localFactor
end AsymptoticClassicalDimension
