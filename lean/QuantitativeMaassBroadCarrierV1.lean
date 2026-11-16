module

public import QuantitativeMaassBroadPacketV1
public import QuantitativeMaassCarrierConvolutionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

def broadTimeSchwartz (L : ℝ) (hL : 0<L) (t : ℝ) : SchwartzMap ℝ ℂ :=
  (broadTimeWeight_compact L hL t).toSchwartzMap (broadTimeWeight_smooth L t)

theorem broadTimeSchwartz_coe (L : ℝ) (hL : 0<L) (t : ℝ) :
    (broadTimeSchwartz L hL t : ℝ → ℂ)=broadTimeWeight L t := rfl

/-- Removing either central phase leaves the same smooth compact
amplitude. The normalizing denominator is uniformly bounded below. -/
def broadTimeCarrier (L t s : ℝ) : ℂ :=
  ((L/(2*cosineSquareMass (broadTimeDensity L) t):ℝ):ℂ)*(broadTimeBase (L*s):ℂ)

theorem broadTimeCarrier_smooth (L t : ℝ) : ContDiff ℝ ∞ (broadTimeCarrier L t) := by
  apply contDiff_const.mul
  exact Complex.ofRealCLM.contDiff.comp
    (broadTimeBase_smooth.comp (contDiff_const.mul contDiff_id))

theorem broadTimeCarrier_support (L : ℝ) (hL : 0<L) (t : ℝ) :
    Function.support (broadTimeCarrier L t) ⊆ Icc (-(1/L)) (1/L) := by
  intro s hs
  apply broadTimeDensity_support L hL
  intro hz
  have hb : broadTimeBase (L*s)=0 :=
    (mul_eq_zero.mp hz).resolve_left hL.ne'
  exact hs (by simp only [broadTimeCarrier,hb,Complex.ofReal_zero,mul_zero])

theorem broadTimeCarrier_compact (L : ℝ) (hL : 0<L) (t : ℝ) :
    HasCompactSupport (broadTimeCarrier L t) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (broadTimeCarrier_support L hL t) isClosed_Icc)

theorem broadTimeWeight_carriers (L t : ℝ) :
    broadTimeWeight L t=timeFrequencyShift t (broadTimeCarrier L t)+
      timeFrequencyShift (-t) (broadTimeCarrier L t) := by
  funext s
  simp only [broadTimeWeight,normalizedCosineWeight,broadTimeDensity,broadTimeCarrier,
    timeFrequencyShift,Pi.add_apply,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Complex.ofReal_cos,Complex.cos,neg_mul,Complex.ofReal_neg]
  ring

/-- Every fixed finite family of amplitude derivatives has a bound
polynomial in the broad width, chosen independently of the centre t. -/
theorem broadTimeCarrier_derivative_bounds (m : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ L : ℝ,1≤L → ∀ t : ℝ,∀ n : ℕ,n≤m → ∀ s : ℝ,
      ‖iteratedDeriv n (broadTimeCarrier L t) s‖≤C*L^(m+1) := by
  let φ : ℝ → ℂ := fun s => (broadTimeBase s:ℂ)
  have hφ : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp broadTimeBase_smooth
  have hc : HasCompactSupport φ := broadTimeBase_compact.comp_left Complex.ofReal_zero
  obtain ⟨C,hC,hbound⟩ := hc.exists_bound_iteratedFDeriv hφ m
  refine ⟨C,hC,?_⟩
  intro L hL t n hn s
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hmass := broadTimeDensity_cosineSquareMass_half L hLp t
  have hden : 0<2*cosineSquareMass (broadTimeDensity L) t := by linarith
  have hcoeff : 0≤L/(2*cosineSquareMass (broadTimeDensity L) t) := by positivity
  have hcoeff' : L/(2*cosineSquareMass (broadTimeDensity L) t)≤L := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hd : ContDiff ℝ ∞ (fun u : ℝ => φ (L*u)) :=
    hφ.comp (contDiff_const.mul contDiff_id)
  change ‖iteratedDeriv n (fun u => ((L/(2*cosineSquareMass (broadTimeDensity L) t):ℝ):ℂ)*
    φ (L*u)) s‖≤_
  rw [iteratedDeriv_const_mul _ (hd.of_le (by simp)).contDiffAt,
    iteratedDeriv_comp_const_smul (hφ.of_le (by simp)) L]
  dsimp only
  rw [norm_mul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hcoeff,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hLp.le n)]
  have hb := hbound n hn (L*s)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hb
  calc
    _ ≤ L*(L^n*C) := mul_le_mul hcoeff'
      (mul_le_mul_of_nonneg_left hb (pow_nonneg hLp.le n)) (by positivity) hLp.le
    _ = C*L^(n+1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) hC

#print axioms broadTimeWeight_carriers
#print axioms broadTimeCarrier_derivative_bounds

end QuantitativeMaass
