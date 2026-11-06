module

public import QuantitativeEulerEndpointAmplifierV1
public import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialPower
open Polynomial

/-- Uniform elementary low-pass energy bound, including both endpoints. -/
theorem scalar_energy {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1) (n : ℕ) :
    x*(1-x)^n≤1/((n:ℝ)+1) := by
  let y := 1-x
  have hy0 : 0≤y := sub_nonneg.mpr hx1
  have hy1 : y≤1 := sub_le_self _ hx0
  have hsum : ((n:ℝ)+1)*y^n≤∑ i∈Finset.range (n+1), y^i := by
    calc
      _ = ∑ _i∈Finset.range (n+1), y^n := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi =>
        pow_le_pow_of_le_one hy0 hy1 (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  have hm := mul_le_mul_of_nonneg_left hsum hx0
  have hg := geom_sum_mul y (n+1)
  have hp := pow_nonneg hy0 (n+1)
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
  dsimp only [y] at hm hg hp ⊢
  nlinarith only [hm,hg,hp]

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- Polynomial initial filter with explicit degree and exact value1 at0. -/
def powerPolynomial (n : ℕ) : ℝ[X] := (1-X)^n

def powerFilter (G : 𝔄) (n : ℕ) : 𝔄 := (1-G)^n

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem powerFilter_aeval (G : 𝔄) (n : ℕ) :
    powerFilter G n=aeval G (powerPolynomial n) := by
  simp only [powerFilter,powerPolynomial,map_pow,map_sub,map_one,aeval_X]

theorem powerFilter_order (G : 𝔄) (hG0 : 0≤G) (hG1 : G≤1) (n : ℕ) :
    0≤powerFilter G n ∧ powerFilter G n≤1 := by
  have hb0 : 0≤1-G := sub_nonneg.mpr hG1
  have hb1 : 1-G≤1 := sub_le_self _ hG0
  exact ⟨CStarAlgebra.pow_nonneg _ n hb0,
    by simpa only [powerFilter,pow_zero] using CStarAlgebra.pow_antitone hb1 hb0 (Nat.zero_le n)⟩

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem powerFilter_fixed (G E : 𝔄) (hGE : G*E=0) (n : ℕ) : powerFilter G n*E=E := by
  have hh : (1-G)*E=E := by rw [sub_mul,one_mul,hGE,sub_zero]
  induction n with
  | zero => simp [powerFilter]
  | succ n ih =>
    change (1-G)^(n+1)*E=E
    rw [pow_succ,mul_assoc,hh]
    exact ih

theorem energy_norm (G : 𝔄) (hG0 : 0≤G) (hG1 : G≤1) (n : ℕ) :
    ‖G*powerFilter G n‖≤1/((n:ℝ)+1) := by
  let z : ℝ[X] := X*(1-X)^n
  have hn : ‖G‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg G hG0).mpr hG1
  have h := norm_cfc_le (a:=G) (f:=z.eval) (by positivity : (0:ℝ)≤1/((n:ℝ)+1))
    (fun x hx => by
      have hx0 := spectrum_nonneg_of_nonneg hG0 hx
      have hx1 : x≤1 := (le_abs_self x).trans
        ((quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ G hx)).trans hn)
      simp only [z,eval_mul,eval_X,eval_pow,eval_sub,eval_one,Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hx0 (pow_nonneg (sub_nonneg.mpr hx1) n))]
      exact scalar_energy hx0 hx1 n)
  simpa only [cfc_polynomial _ G (IsSelfAdjoint.of_nonneg hG0),z,map_mul,map_pow,map_sub,
    map_one,aeval_X,powerFilter] using h

theorem sandwiched_energy_norm (G : 𝔄) (hG0 : 0≤G) (hG1 : G≤1) (m : ℕ) :
    ‖powerFilter G m*G*powerFilter G m‖≤1/(((2*m:ℕ):ℝ)+1) := by
  have hc : Commute G (1-G) := (Commute.one_right G).sub_right (Commute.refl G)
  have he : powerFilter G m*G*powerFilter G m=G*powerFilter G (2*m) := by
    rw [powerFilter,powerFilter,← (hc.pow_right m).eq,mul_assoc,← pow_add]
    congr 2
    omega
  rw [he]
  exact energy_norm G hG0 hG1 (2*m)

#print axioms scalar_energy
#print axioms powerFilter_order
#print axioms powerFilter_fixed
#print axioms energy_norm
#print axioms sandwiched_energy_norm
end QuantitativeEulerEndpointInitialPower
