module

public import QuantitativeArithmeticShiftedSieveProgressionBoundV1
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Filter QuantitativeArithmeticShiftedSieveProgression

/-- The natural eighth root suffices; no asymptotics for a moving sieve
level are needed. All dependence on the fixed modulus is in this explicit
threshold, while the final upper-bound constant is absolute. -/
def shiftedSieveUpperThreshold (R : ℕ) : ℕ :=
  (max (R^2) (max 2 (16*Nat.totient R)))^8

theorem log_eighth_power_comparison (x z : ℝ) (hx : 0 < x) (hz : 2 ≤ z)
    (hupper : x ≤ (z+1)^8) :
    Real.log x ≤ 16*Real.log z ∧ Real.log x ≤ 8*z := by
  have hlog := Real.log_le_log hx hupper
  rw [Real.log_pow] at hlog
  have hzsq : z+1 ≤ z^2 := by nlinarith
  have hlogz := Real.log_le_log (by linarith : 0 < z+1) hzsq
  rw [Real.log_pow] at hlogz
  have hlinear := Real.log_le_sub_one_of_pos (by linarith : 0 < z+1)
  norm_num at hlog hlogz
  constructor <;> linarith

/-- A fully explicit fixed-progression prime-count upper bound. The sieve
weights, their remainder, and the logarithmic denominator estimate are
all previously proved; this theorem merely chooses the concrete level.
It is uniform in the residue b, including non-unit residues. -/
theorem progressionPrimeCount_upper_of_threshold (R b x : ℕ) (hR : 0 < R)
    (hx : shiftedSieveUpperThreshold R ≤ x) :
    (progressionPrimeCount R b x : ℝ) ≤
      65*(x : ℝ)/((Nat.totient R : ℝ)*Real.log x) := by
  let z := Nat.nthRoot 8 x
  have hcut : max (R^2) (max 2 (16*Nat.totient R)) ≤ z := by
    exact (Nat.le_nthRoot_iff (by norm_num : (8 : ℕ) ≠ 0)).mpr hx
  have hRz : R^2 ≤ z := (le_max_left _ _).trans hcut
  have hz2 : 2 ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans hcut)
  have hφz : 16*Nat.totient R ≤ z :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hcut)
  have hlow : z^8 ≤ x := Nat.pow_nthRoot_le (Or.inl (by norm_num : (8 : ℕ) ≠ 0))
  have hupp : x < (z+1)^8 := Nat.lt_pow_nthRoot_add_one (by norm_num : (8 : ℕ) ≠ 0) x
  have hz2r : (2 : ℝ) ≤ z := by exact_mod_cast hz2
  have hz1r : (1 : ℝ) ≤ z := by linarith
  have hzpos : (0 : ℝ) < z := by linarith
  have hlowr : (z : ℝ)^8 ≤ (x : ℝ) := by exact_mod_cast hlow
  have hupper : (x : ℝ) ≤ ((z : ℝ)+1)^8 := by exact_mod_cast Nat.le_of_lt hupp
  have hx1 : (1 : ℝ) < x := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hz2r 8
    norm_num at hp
    linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hφ : (0 : ℝ) < Nat.totient R := by exact_mod_cast Nat.totient_pos.mpr hR
  obtain ⟨hlogratio, hloglin⟩ := log_eighth_power_comparison (x : ℝ) (z : ℝ)
    hxpos hz2r hupper
  have hz14 : (z : ℝ) ≤ (z : ℝ)^4 := by
    simpa using pow_le_pow_right₀ hz1r (by norm_num : 1 ≤ 4)
  have hz13 : (z : ℝ) ≤ (z : ℝ)^3 := by
    simpa using pow_le_pow_right₀ hz1r (by norm_num : 1 ≤ 3)
  have hφcube : 16*(Nat.totient R : ℝ) ≤ (z : ℝ)^3 := by
    have hh : 16*(Nat.totient R : ℝ) ≤ (z : ℝ) := by exact_mod_cast hφz
    exact hh.trans hz13
  have herrmul : ((z : ℝ)^4+(z : ℝ))*(Nat.totient R : ℝ)*Real.log x ≤ (x : ℝ) := by
    calc
      _ ≤ (2*(z : ℝ)^4)*(Nat.totient R : ℝ)*(8*(z : ℝ)) := by
        gcongr
        nlinarith
      _ = (16*(Nat.totient R : ℝ))*(z : ℝ)^5 := by ring
      _ ≤ (z : ℝ)^3*(z : ℝ)^5 := mul_le_mul_of_nonneg_right hφcube (by positivity)
      _ = (z : ℝ)^8 := by ring
      _ ≤ (x : ℝ) := hlowr
  have herr : (z : ℝ)^4+(z : ℝ) ≤
      (x : ℝ)/((Nat.totient R : ℝ)*Real.log x) := by
    apply (le_div_iff₀ (mul_pos hφ hlogx)).mpr
    simpa only [mul_assoc] using herrmul
  have hmain : 4*(x : ℝ)/((Nat.totient R : ℝ)*Real.log z) ≤
      64*(x : ℝ)/((Nat.totient R : ℝ)*Real.log x) := by
    apply (div_le_div_iff₀ (mul_pos hφ hlogz) (mul_pos hφ hlogx)).mpr
    calc
      _ = (4*(x : ℝ)*(Nat.totient R : ℝ))*Real.log x := by ring
      _ ≤ (4*(x : ℝ)*(Nat.totient R : ℝ))*(16*Real.log z) :=
        mul_le_mul_of_nonneg_left hlogratio (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 4*(x : ℝ)/((Nat.totient R : ℝ)*Real.log z)+(z : ℝ)^4+(z : ℝ) :=
      progressionPrimeCount_log_bound R b x z hR (by omega) hRz
    _ = 4*(x : ℝ)/((Nat.totient R : ℝ)*Real.log z)+((z : ℝ)^4+(z : ℝ)) := by ring
    _ ≤ 64*(x : ℝ)/((Nat.totient R : ℝ)*Real.log x)+
        (x : ℝ)/((Nat.totient R : ℝ)*Real.log x) := add_le_add hmain herr
    _ = _ := by ring

/-- The absolute constant 65 is independent of R and of b; only the
eventual threshold depends on the fixed modulus. -/
theorem eventually_progressionPrimeCount_upper (R : ℕ) (hR : 0 < R) :
    ∀ᶠ x : ℕ in atTop, ∀ b : ℕ, (progressionPrimeCount R b x : ℝ) ≤
      65*(x : ℝ)/((Nat.totient R : ℝ)*Real.log x) :=
  eventually_atTop.mpr ⟨shiftedSieveUpperThreshold R,
    fun x hx b => progressionPrimeCount_upper_of_threshold R b x hR hx⟩

#print axioms log_eighth_power_comparison
#print axioms progressionPrimeCount_upper_of_threshold
#print axioms eventually_progressionPrimeCount_upper

end QuantitativeArithmetic
