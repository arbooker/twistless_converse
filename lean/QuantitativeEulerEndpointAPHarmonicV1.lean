module

public import QuantitativeEulerEndpointAPFiniteV1
public import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset

/-- An explicit positive exponent sufficient for summability of sieve
exceptions; sharp AP Mertens asymptotics are not needed. -/
def apExponent (M : ℕ) : ℝ := (M.totient : ℝ)⁻¹/(2*Real.log 2)

theorem apExponent_pos (M : ℕ) [NeZero M] : 0<apExponent M := by
  unfold apExponent
  apply div_pos (inv_pos.mpr ?_) (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  exact_mod_cast Nat.totient_pos.mpr (NeZero.pos M)

/-- Quantitative reciprocal-prime mass in every unit residue class, at
every finite cutoff Y>=4. This is derived from the actual Dirichlet pole,
not assumed from a prime number theorem or from a density statement. -/
theorem primeReciprocal_loglog_lower {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) :
    ∃ C : ℝ, 0≤C ∧ ∀ Y : ℕ, 4≤Y →
      apExponent M*Real.log (Real.log (Y : ℝ))-C≤
        ∑ n∈range Y, primeReciprocal a n := by
  obtain ⟨C,hC,hfinite⟩ := finite_primeReciprocal_dyadic_lower a ha
  let b : ℝ := (M.totient : ℝ)⁻¹
  have hb : 0<b := inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos M))
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hc := apExponent_pos M
  have hid : apExponent M*Real.log 2=b/2 := by
    dsimp [apExponent,b]
    field_simp
  refine ⟨C+b/2,by positivity,fun Y hY => ?_⟩
  have hYR : (4 : ℝ)≤Y := by exact_mod_cast hY
  have hYpos : (0 : ℝ)<Y := by linarith
  have hlY1 : 1≤Real.log (Y : ℝ) :=
    (Real.le_log_iff_exp_le hYpos).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have hlY : 0<Real.log (Y : ℝ) := by linarith
  let J : ℕ := ⌊Real.log (Real.log (Y : ℝ))/Real.log 2⌋₊
  have hratio : 0≤Real.log (Real.log (Y : ℝ))/Real.log 2 :=
    div_nonneg (Real.log_nonneg hlY1) h2.le
  have hJle : (J : ℝ)≤Real.log (Real.log (Y : ℝ))/Real.log 2 := Nat.floor_le hratio
  have hJlt : Real.log (Real.log (Y : ℝ))/Real.log 2<(J : ℝ)+1 := Nat.lt_floor_add_one _
  have hp : (2 : ℝ)^J≤Real.log (Y : ℝ) := by
    apply (Real.log_le_log_iff (pow_pos (by norm_num) J) hlY).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ h2).mp hJle
  have hdyadic : dyadic J*(2 : ℝ)^J=1 := by
    rw [dyadic,← mul_pow]
    norm_num
  have hcut : 1≤dyadic J*Real.log (Y : ℝ) := by
    rw [← hdyadic]
    exact mul_le_mul_of_nonneg_left hp (dyadic_pos J).le
  have hf := hfinite J Y (by omega) hcut
  have hJ : Real.log (Real.log (Y : ℝ))≤((J : ℝ)+1)*Real.log 2 :=
    (div_le_iff₀ h2).mp hJlt.le
  have hm := mul_le_mul_of_nonneg_left hJ hc.le
  dsimp only [b] at hid ⊢
  nlinarith

#print axioms apExponent_pos
#print axioms primeReciprocal_loglog_lower
end QuantitativeEulerEndpointAP
