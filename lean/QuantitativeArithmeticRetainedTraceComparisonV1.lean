module

public import QuantitativeArithmeticRetainedWeightedTraceV1
public import QuantitativeArithmeticRetainedTraceCutoffV1
public import QuantitativeEulerEndpointWeightedTraceV1
public import QuantitativeHolomorphicGrowingPeriodizationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedTraceComparison
open ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticDiagonalTrace
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedPreparedReconstruction QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedFourierMajorant QuantitativeHolomorphic InnerProductSpace
open AsymptoticCylinderModeComparison AsymptoticFiniteBranch AsymptoticUnweightedKernel
open scoped InnerProduct
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ)
    (hR₀ : ∀p∈R₀,p.Prime) (hN : 0<N) (P : Parameters A)

/-- Cylinder realization of the literal finite mixed reconstruction. -/
def physicalCylinder (τ : ℝ) (e : Sector N) (h : ℕ) :=
  polynomialNormalizedReconstruction
    (physicalScaled A P hR₀ hN (rawTolerance A P τ) (lowerHeight A P τ) e (h+1))
    (newtonDepth A P τ)

theorem physicalCylinder_norm (τ : ℝ) (e : Sector N) (h : ℕ) :
    ‖physicalCylinder A hR₀ hN P τ e h‖≤1 :=
  polynomialNormalizedReconstruction_norm_le _ (physicalScaled_norm A P hR₀ hN _ _ e (h+1)) _

theorem physicalCylinder_left_height (τ : ℝ) (e : Sector N) (h : ℕ) :
    (upperProjection (lowerHeight A P τ)).comp (physicalCylinder A hR₀ hN P τ e h)=
      physicalCylinder A hR₀ hN P τ e h :=
  QuantitativeArithmeticRetainedTraceCutoff.finite_left_height A hR₀ hN P _ _ e (h+1) _

/-- Only reconstruction changes here. The entire nested filter stays fixed,
so the trace error has no factor depending on the number of filter steps. -/
theorem finite_reconstruction_trace_error {τ : ℝ} (hτ : 0<τ) (hτ1 : 2*τ≤1)
    (h : ℕ) (e : Sector N)
    (F : AsymptoticCylinderTerminal.Space P.ε →L[ℂ] AsymptoticCylinderTerminal.Space P.ε)
    (hF : ‖F‖≤1) :
    let W := holomorphicSpace (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos
    let fb := fourierBasis (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos
    let U := QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e
    let V := physicalCylinder A hR₀ hN P τ e h
    ‖trace fb (compressedSandwich V F W)-trace fb (compressedSandwich U F W)‖/(4*h+2:ℝ)≤
      (2+2*QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P (newtonDepth A P τ)*
        majorantConstant (exponent A P+4) (4*Real.pi) P.ε)*Real.sqrt (2*τ) := by
  intro W fb U V
  have hU : ‖U‖≤1 := QuantitativeArithmeticRetainedFilterTrace.reconstruction_norm A hR₀ hN P h e
  have hV : ‖V‖≤1 := physicalCylinder_norm A hR₀ hN P τ e h
  have herr : ‖V-U‖≤τ := scheduled_physical_error A P hR₀ hN hτ e (h+1)
  have hC : 0≤QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P (newtonDepth A P τ) :=
    (sq_nonneg _).trans (le_max_left _ _)
  have hbU (l : ℕ) : ‖(⟪compressedSandwich U F W (fb l),fb l⟫_ℂ).re‖≤
      QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P (newtonDepth A P τ)*
        modeRatio (2*h) (exponent A P+4) (4*Real.pi) P.ε (l+1) := by
    apply (compressedSandwich_diagonal_bound U F W (fb l)).trans
    apply (mul_le_mul_of_nonneg_right hF (sq_nonneg _)).trans
    rw [one_mul]
    exact (normalized_fourier_gram A hR₀ hN P h e l).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (modeRatio_nonneg _ _ _ _ P.epsilon_pos))
  have hbV (l : ℕ) : ‖(⟪compressedSandwich V F W (fb l),fb l⟫_ℂ).re‖≤
      QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P (newtonDepth A P τ)*
        modeRatio (2*h) (exponent A P+4) (4*Real.pi) P.ε (l+1) := by
    apply (compressedSandwich_diagonal_bound V F W (fb l)).trans
    apply (mul_le_mul_of_nonneg_right hF (sq_nonneg _)).trans
    rw [one_mul]
    exact (finite_fourier_gram A hR₀ hN P _ _ h e _ l).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (modeRatio_nonneg _ _ _ _ P.epsilon_pos))
  have hd : ‖compressedSandwich V F W-compressedSandwich U F W‖≤2*τ := by
    apply (orthogonalCompression_sub_norm_le W _ _).trans
    have hh := sandwich_sub_norm_le V U F F hF hF
    simp only [sub_self,norm_zero,mul_zero,add_zero] at hh
    exact hh.trans (mul_le_mul (show ‖V‖+‖U‖≤2 by linarith) herr (norm_nonneg _) (by norm_num))
  have ht := normalized_trace_sub_le_sqrt_of_absolute_majorants fb _ _ (2*h) (exponent A P+4)
    (by positivity : 0<4*Real.pi) P.epsilon_pos hC (by positivity : 0<2*τ) hτ1 hd hbV hbU
  convert ht using 1
  push_cast
  ring

/-- Output truncation for an arbitrary fixed terminal contraction. -/
theorem finite_upper_trace_error (τ H : ℝ) (hH : 0<H) (h : ℕ) (e : Sector N)
    (F : AsymptoticCylinderTerminal.Space P.ε →L[ℂ] AsymptoticCylinderTerminal.Space P.ε)
    (hF : ‖F‖≤1) :
    let t := exponent A P+4
    let fb := fourierBasis (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos
    let V := physicalCylinder A hR₀ hN P τ e h
    let B := (3/2:ℝ)^newtonDepth A P τ
    ‖trace fb (compressedSandwich V F (holomorphicSpace (2*h) t
        (by positivity : 0<4*Real.pi) P.epsilon_pos))-
      upperCutTrace V F (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos H‖/(2*h+2:ℝ)≤
      upperCutError (B^2*(1+majorantConstant t (4*Real.pi) P.ε)) B 1
        (massBound (2*h) t (4*Real.pi) H/(2*h+2:ℝ)) := by
  intro t fb V B
  let R := finiteWeighted A hR₀ hN P (rawTolerance A P τ) (lowerHeight A P τ) e (h+1) (newtonDepth A P τ)
  have ht := factored_upperCut_trace_bound R F (finiteWeighted_norm A hR₀ hN P _ _ e (h+1) _)
    hF (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos hH
  have hv : (inclusion P.epsilon_pos).comp R=V := (finite_weighted A hR₀ hN P _ _ e (h+1) _).symm
  rw [hv] at ht
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at ht
  apply ht.trans
  have hm := div_le_div_of_nonneg_right
    (upperCompression_trace_le_massBound (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos hH)
    (by positivity : (0:ℝ)≤2*h+2)
  unfold upperCutError
  gcongr

/-- Weighted/unweighted comparison after cutting the output only. -/
theorem weighted_trace_error {τ : ℝ} (hτ : 0<τ) (H : ℝ) (h : ℕ) (e : Sector N)
    (F : AsymptoticCylinderTerminal.Space P.ε →L[ℂ] AsymptoticCylinderTerminal.Space P.ε)
    (hF : ‖F‖≤1) :
    ‖upperCutTrace (physicalCylinder A hR₀ hN P τ e h) F (2*h) (exponent A P+4)
      (by positivity : 0<4*Real.pi) P.epsilon_pos H-
      upperCutTrace (physicalCylinder A hR₀ hN P τ e h) F (2*h) 0
      (by positivity : 0<4*Real.pi) P.epsilon_pos H‖/(2*h+2:ℝ)≤
      (2*Real.sqrt (localizedErrorBound (exponent A P+4) (4*Real.pi) (lowerHeight A P τ))*
        Real.sqrt (massSlope (exponent A P+4) (4*Real.pi) (lowerHeight A P τ)))*
        (Real.sqrt (2*h+2:ℝ))⁻¹ := by
  have ht := QuantitativeEulerEndpointWeightedTrace.upper_weighted_difference (2*h) (exponent A P+4)
    P.epsilon_pos (lowerHeight_pos A P hτ) H (physicalCylinder A hR₀ hN P τ e h) F
    (physicalCylinder_norm A hR₀ hN P τ e h) hF (physicalCylinder_left_height A hR₀ hN P τ e h)
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using ht

/-- All three analytic errors, before choosing the scalar accuracy schedule. -/
def traceError (τ H : ℝ) (h : ℕ) : ℝ :=
  let t := exponent A P+4
  let n := newtonDepth A P τ
  let B := (3/2:ℝ)^n
  2*((2+2*QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P n*
      majorantConstant t (4*Real.pi) P.ε)*Real.sqrt (2*τ))+
  upperCutError (B^2*(1+majorantConstant t (4*Real.pi) P.ε)) B 1
    (massBound (2*h) t (4*Real.pi) H/(2*h+2:ℝ))+
  (2*Real.sqrt (localizedErrorBound t (4*Real.pi) (lowerHeight A P τ))*
    Real.sqrt (massSlope t (4*Real.pi) (lowerHeight A P τ)))*(Real.sqrt (2*h+2:ℝ))⁻¹

/-- The exact weighted reconstruction trace is bounded by the unweighted
output-truncated finite trace, uniformly over all terminal contractions. -/
theorem trace_le_unweighted {τ : ℝ} (hτ : 0<τ) (hτ1 : 2*τ≤1)
    (H : ℝ) (hH : 0<H) (h : ℕ) (e : Sector N)
    (F : AsymptoticCylinderTerminal.Space P.ε →L[ℂ] AsymptoticCylinderTerminal.Space P.ε)
    (hF : ‖F‖≤1) :
    let t := exponent A P+4
    let fb := fourierBasis (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos
    let W := holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos
    trace fb (compressedSandwich (QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e) F W)/(2*h+2:ℝ)≤
      upperCutTrace (physicalCylinder A hR₀ hN P τ e h) F (2*h) 0
        (by positivity : 0<4*Real.pi) P.epsilon_pos H/(2*h+2:ℝ)+traceError A P τ H h := by
  intro t fb W
  have he := finite_reconstruction_trace_error A hR₀ hN P hτ hτ1 h e F hF
  have hu := finite_upper_trace_error A hR₀ hN P τ H hH h e F hF
  have hw := weighted_trace_error A hR₀ hN P hτ H h e F hF
  have hk : (0:ℝ)<2*h+2 := by positivity
  have hk' : (0:ℝ)<4*h+2 := by positivity
  have he0 : 0≤(2+2*QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P (newtonDepth A P τ)*
      majorantConstant t (4*Real.pi) P.ε)*Real.sqrt (2*τ) := (div_nonneg (norm_nonneg _) hk'.le).trans he
  have he' := (div_le_iff₀ hk').mp he
  have hu' := (div_le_iff₀ hk).mp hu
  have hw' := (div_le_iff₀ hk).mp hw
  rw [Real.norm_eq_abs] at he' hu' hw'
  have ha := (abs_le.mp he').1
  have hb := (abs_le.mp hu').2
  have hc := (abs_le.mp hw').2
  have hr := mul_le_mul_of_nonneg_left
    (show (4*h+2:ℝ)≤2*(2*h+2:ℝ) by linarith) he0
  apply (div_le_iff₀ hk).mpr
  unfold traceError
  dsimp only
  nlinarith only [ha,hb,hc,hr,div_mul_cancel₀
    (upperCutTrace (physicalCylinder A hR₀ hN P τ e h) F (2*h) 0
      (by positivity : 0<4*Real.pi) P.epsilon_pos H) hk.ne']

#print axioms finite_reconstruction_trace_error
#print axioms finite_upper_trace_error
#print axioms weighted_trace_error
#print axioms trace_le_unweighted
end QuantitativeArithmeticRetainedTraceComparison
