module

public import QuantitativeMaassParametersV1

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass

/-- The finite inverse-cap mass costs only an exponential in propagation
radius, independent of the chosen upper cusp height. -/
theorem inverse_band_mass_exp_bound (ν : ℕ) {R : ℝ} (hR : 1≤R) :
    let J := ⌈(ν:ℝ)*R+1⌉₊
    ((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)≤Real.exp ((3*(ν:ℝ)+7)*R) := by
  intro J
  have hR0 : 0≤R := zero_le_one.trans hR
  have hJ : (J:ℝ)≤(ν:ℝ)*R+2 := by
    have hh := (Nat.ceil_lt_add_one (by positivity : 0≤(ν:ℝ)*R+1)).le
    change (J:ℝ)≤(ν:ℝ)*R+1+1 at hh
    linarith
  have hmass : ((2*J+1:ℕ):ℝ)≤Real.exp (2*(J:ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      Real.add_one_le_exp (2*(J:ℝ))
  calc
    _ ≤ Real.exp (2*(J:ℝ))*Real.exp ((J:ℝ)+1) :=
      mul_le_mul_of_nonneg_right hmass (Real.exp_pos _).le
    _ = Real.exp (3*(J:ℝ)+1) := by rw [←Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

#print axioms inverse_band_mass_exp_bound
end QuantitativeMaass
