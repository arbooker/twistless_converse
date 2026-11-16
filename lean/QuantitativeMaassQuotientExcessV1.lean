module

public import QuantitativeMaassWindowTailTraceV1
public import QuantitativeMaassCuspCoverIntegralV1
public import QuantitativeMaassTranslatedIdentityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand QuantitativeSpectralObservability
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The actual squared-window identity contribution is nonnegative at all
endpoints, independently of any limiting asymptotic. -/
theorem windowIdentityContribution_re_nonneg (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    0≤(windowIdentityContribution K hc R hR a b).re := by
  let f := windowTimeSchwartz K hc R hR a b
  have hf : Function.Even f := symmetricWindowTimeTest_even K he R a b
  have hr : ∀ u,star (f u)=f u := symmetricWindowTimeTest_real K he R a b
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R a b hR
  change 0≤(abelProfile (evenCoshLift (timeConvolution f f)) 1).re
  rw [abelProfile_timeSquare_diagonal f hf hr hfc,integral_complex_ofReal]
  have hp : (1/(4*Real.pi):ℂ)=((1/(4*Real.pi):ℝ):ℂ) := by push_cast; rfl
  rw [hp,←Complex.ofReal_mul,Complex.ofReal_re]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro r
  have hh := windowPlancherelWeight_nonneg r
  change 0≤r*Real.tanh (Real.pi*r) at hh
  convert mul_nonneg (sq_nonneg ‖cosinePacket f r‖) hh using 1
  ring

/-- Cover only the positive excess, so the leading constant multiplies the
true finite quotient volume rather than the larger overlapping raw cover. -/
theorem quotient_positive_excess_cover (N : ℕ) (hN : 0<N) (Y I : ℝ) (hI : 0≤I)
    (F : ℍ → ℝ) (hF : Measurable F) (hinv : ∀ γ : gamma N,∀ z,F (γ.val•z)=F z) :
    (∫⁻ z,ENNReal.ofReal (F z) ∂quotientMeasure N)≤
      ENNReal.ofReal I*quotientMeasure N univ+
        (∫⁻ z in wideCompactCover N Y,ENNReal.ofReal (max (F z-I) 0))+
        ∑' q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ∑' b : Bool,
          ∫⁻ z in cuspTailSet N Y,ENNReal.ofReal (max (F (cuspAction (globalCuspChart N q b) z)-I) 0) := by
  let E := fun z => ENNReal.ofReal (max (F z-I) 0)
  have hE : Measurable E := ((hF.sub_const I).max measurable_const).ennreal_ofReal
  have hEinv : ∀ γ : gamma N,∀ z,E (γ.val•z)=E z := by
    intro γ z
    simp only [E,hinv]
  have hcover := quotient_mass_le_core_cusps N hN Y E hE hEinv
  have hpoint (z : ℍ) : ENNReal.ofReal (F z)≤ENNReal.ofReal I+E z := by
    have hh : F z≤I+max (F z-I) 0 := by linarith [le_max_left (F z-I) 0]
    apply (ENNReal.ofReal_le_ofReal hh).trans_eq
    exact ENNReal.ofReal_add hI (le_max_right _ _)
  calc
    _ ≤ ∫⁻ z,(ENNReal.ofReal I+E z) ∂quotientMeasure N := lintegral_mono hpoint
    _ = ENNReal.ofReal I*quotientMeasure N univ+∫⁻ z,E z ∂quotientMeasure N := by
      rw [lintegral_add_left measurable_const,lintegral_const]
    _ ≤ _ := by
      have hh := add_le_add_left hcover (ENNReal.ofReal I*quotientMeasure N univ)
      simpa only [add_assoc,add_comm,add_left_comm,E] using hh

/-- The finite-family excess is bounded by the actual nonidentity remainder. -/
theorem window_finite_energy_excess_bound {ι : Type*} (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (v : ι → AutomorphicSpace N)
    (hv : Orthonormal ℂ v) (S : Finset ι) (z : ℍ) :
    max ((∑ i∈S,‖inner ℂ (windowAbelColumn N K he hc R hR a b z) (v i)‖^2)-
      (windowIdentityContribution K hc R hR a b).re) 0≤
        ‖windowGeometricRemainder N K hc R hR a b z‖ := by
  have hh := hv.sum_inner_products_le (s:=S) (windowAbelColumn N K he hc R hR a b z)
  have hs : (∑ i∈S,‖inner ℂ (windowAbelColumn N K he hc R hR a b z) (v i)‖^2)≤
      ‖windowAbelColumn N K he hc R hR a b z‖^2 := by
    simpa only [norm_inner_symm] using hh
  clear hh
  rw [windowAbelColumn_norm_square N K he hc R hR a b] at hs
  apply max_le _ (norm_nonneg _)
  have hreal := Complex.re_le_norm (windowGeometricRemainder N K hc R hR a b z)
  linarith

#print axioms windowIdentityContribution_re_nonneg
#print axioms quotient_positive_excess_cover
#print axioms window_finite_energy_excess_bound

end QuantitativeMaass
