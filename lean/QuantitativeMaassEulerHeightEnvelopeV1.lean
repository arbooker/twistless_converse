module

public import QuantitativeMaassEulerHeightDecayV1
public import FinitenessHeightEnvelopeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Each positive-height tail has an actual finite polynomially weighted
bound, derived from the Fourier series rather than assumed globally. -/
theorem principalEulerWave_height_bound {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (r : ℝ) (σ s : ℕ)
    (a : ℝ) (ha : 0<a) : ∃ C : ℝ,0≤C ∧ ∀ x y : ℝ,a≤y →
      y^s*‖principalEulerWave b r σ (x,y)‖≤C := by
  let S := ∑' n,principalMomentMajorant b 0 0 (2*Real.pi) (a/2) n
  have hS : 0≤S := tsum_nonneg (fun n => by
    unfold principalMomentMajorant
    have hm := MaassKBessel.zero_moment_nonneg 0 (2*Real.pi*(a/2))
    positivity)
  let B := (s.factorial:ℝ)/Real.pi^s+((s+1).factorial:ℝ)/Real.pi^(s+1)
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨2*B*S,by positivity,?_⟩
  intro x y hy
  have hy0 : 0<y := ha.trans_le hy
  have hsqrt : Real.sqrt y≤1+y := by
    have hh := Real.sq_sqrt hy0.le
    nlinarith [Real.sqrt_nonneg y]
  have hc := principalWeightedSeries_exponential_bound hb r 0 0 σ a ha x y hy
  rw [principalWeightedSeries_zero] at hc
  have he : y^s*Real.sqrt y*Real.exp (-Real.pi*y)≤B := by
    calc
      _ ≤ y^s*(1+y)*Real.exp (-Real.pi*y) := by gcongr
      _ = y^s*Real.exp (-Real.pi*y)+y^(s+1)*Real.exp (-Real.pi*y) := by rw [pow_succ]; ring
      _ ≤ _ := add_le_add (MaassKBessel.pow_mul_exp_bound s Real.pi_pos hy0.le)
        (MaassKBessel.pow_mul_exp_bound (s+1) Real.pi_pos hy0.le)
  unfold principalEulerWave
  dsimp only
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg y)]
  calc
    _ ≤ y^s*(Real.sqrt y*((2*Real.exp (-Real.pi*y))*S)) := by gcongr
    _ = 2*(y^s*Real.sqrt y*Real.exp (-Real.pi*y))*S := by ring
    _ ≤ _ := by gcongr

/-- The envelope required by strict height reconstruction is finite on every
positive tail, with no common coefficient-growth exponent. -/
theorem principalEulerWave_tail_bddAbove {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (r : ℝ) (σ s : ℕ)
    (a : ℝ) (ha : 0<a) :
    BddAbove (FinitenessHeightEnvelope.tailSet (fun z : ℝ×ℝ => z.2)
      (fun z => z.2^s*‖principalEulerWave b r σ z‖) a) := by
  obtain ⟨C,_,hC⟩ := principalEulerWave_height_bound hb r σ s a ha
  refine ⟨C,?_⟩
  rintro v ⟨z,hz,rfl⟩
  exact hC z.1 z.2 hz

theorem principalEulerWave_tail_nonempty (b : ℕ → ℂ) (r : ℝ) (σ s : ℕ) (a : ℝ) :
    (FinitenessHeightEnvelope.tailSet (fun z : ℝ×ℝ => z.2)
      (fun z => z.2^s*‖principalEulerWave b r σ z‖) a).Nonempty := by
  exact ⟨a^s*‖principalEulerWave b r σ (0,a)‖,(0,a),le_rfl,rfl⟩

#print axioms principalEulerWave_height_bound
#print axioms principalEulerWave_tail_bddAbove
#print axioms principalEulerWave_tail_nonempty

end QuantitativeMaass
