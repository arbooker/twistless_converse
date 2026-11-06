module

public import QuantitativeArithmeticRetainedFiniteScheduleV1
public import AsymptoticCylinderHeightCutoffV1
public import AsymptoticRegularHeightCutoffV1
public import QuantitativeHolomorphicNewtonCoefficientsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFiniteNormalization
open ContinuousLinearMap AsymptoticSectorSigns AsymptoticFiniteBranch
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedSectorReconstruction
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedCylinderNormalization (bound bound_one_le gramLower gramLower_pos gramLower_le_one)
open QuantitativeHolomorphic

section OperatorEstimates
variable {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem contract_left (A : F →L[ℂ] G) (B : E →L[ℂ] F) (hA : ‖A‖≤1) : ‖A.comp B‖≤‖B‖ :=
  (opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_right hA (norm_nonneg B)).trans_eq (one_mul _))

theorem contract_right (A : F →L[ℂ] G) (B : E →L[ℂ] F) (hB : ‖B‖≤1) : ‖A.comp B‖≤‖A‖ :=
  (opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left hB (norm_nonneg A)).trans_eq (mul_one _))

/-- A capped inclusion makes removing small output heights uniformly
small, independently of the details of the reconstruction. -/
theorem cut_error (I Q : F →L[ℂ] F) (R V : E →L[ℂ] F)
    {δ η B : ℝ} (hI : ‖I‖≤1) (hQ : ‖Q‖≤1) (hcut : ‖I-Q.comp I‖≤η)
    (hη : 0≤η) (hR : ‖R‖≤B) (herr : ‖V-R‖≤δ) :
    ‖Q.comp (I.comp V)-I.comp R‖≤δ+η*B := by
  have hv : ‖Q.comp (I.comp V)-Q.comp (I.comp R)‖≤δ := by
    rw [←comp_sub,←comp_sub]
    exact (contract_left Q _ hQ).trans ((contract_left I _ hI).trans herr)
  have hr : ‖Q.comp (I.comp R)-I.comp R‖≤η*B := by
    rw [norm_sub_rev,←comp_assoc,←sub_comp]
    exact (opNorm_comp_le _ _).trans (mul_le_mul hcut hR (norm_nonneg R) hη)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (Q.comp (I.comp R)) _).trans (add_le_add hv hr)
end OperatorEstimates

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ) (P : Parameters A)
    (hS : ∀p∈S,p.Prime) (hN : 0<N)

def hyperFinite (δ : ℝ) (e : Sector N) (m : ℕ) :=
  (holomorphicSum (QuantitativeArithmeticRetainedFiniteSchedule.expression A P hS hN δ e) m).comp
    (QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL

def cylinderFinite (δ : ℝ) (e : Sector N) (m : ℕ) :=
  AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint.comp
    ((hyperFinite A P hS hN δ e m).comp (QuantitativeArithmeticRetainedCylinderExtension.terminalLift A P))

theorem hyperFinite_norm (δ : ℝ) (e : Sector N) (m : ℕ) :
    ‖hyperFinite A P hS hN δ e m‖≤bound A P := by
  have hs : ‖(QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro g
    simp
  exact (contract_right _ _ hs).trans ((holomorphicSum_norm_le _ m).trans
    (QuantitativeArithmeticRetainedFiniteSchedule.expression_mass A P hS hN δ e))

theorem cylinderFinite_norm (δ : ℝ) (e : Sector N) (m : ℕ) :
    ‖cylinderFinite A P hS hN δ e m‖≤bound A P :=
  (contract_left _ _ AsymptoticCylinderReconstruction.lift_adjoint_norm_le).trans
    ((contract_right _ _ (QuantitativeArithmeticRetainedCylinderExtension.terminalLift_norm_le A P)).trans
      (hyperFinite_norm A P hS hN δ e m))

theorem cylinderFinite_error {δ : ℝ} (hδ : 0<δ) (e : Sector N) (m : ℕ) :
    ‖cylinderFinite A P hS hN δ e m-
      QuantitativeArithmeticRetainedCylinderExtension.extension A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m‖≤δ := by
  change ‖AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint.comp
    ((hyperFinite A P hS hN δ e m).comp (QuantitativeArithmeticRetainedCylinderExtension.terminalLift A P))-
    AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint.comp
    ((QuantitativeArithmeticRetainedTerminalExtension.extension A hS hN P
      (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m).comp
      (QuantitativeArithmeticRetainedCylinderExtension.terminalLift A P))‖≤δ
  rw [←comp_sub,←sub_comp]
  exact (contract_left _ _ AsymptoticCylinderReconstruction.lift_adjoint_norm_le).trans
    ((contract_right _ _ (QuantitativeArithmeticRetainedCylinderExtension.terminalLift_norm_le A P)).trans
      (QuantitativeArithmeticRetainedFiniteSchedule.physical_error A P hS hN hδ e m))

def regularFinite (δ : ℝ) (e : Sector N) (z : UpperHalfPlane) :=
  (regularSum (QuantitativeArithmeticRetainedFiniteSchedule.expression A P hS hN δ e) z).comp
    (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL

theorem regularFinite_norm (δ : ℝ) (e : Sector N) (z : UpperHalfPlane) :
    ‖regularFinite A P hS hN δ e z‖≤bound A P := by
  have hs : ‖(QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro g
    simp
  exact (contract_right _ _ hs).trans ((regularSum_norm_le _ z).trans
    (QuantitativeArithmeticRetainedFiniteSchedule.expression_mass A P hS hN δ e))

/-- The same explicit low-height loss in physical and regular representations. -/
def approximationError (δ Y : ℝ) : ℝ := δ+Y/P.ε*bound A P

def physicalScaled (δ Y : ℝ) (e : Sector N) (m : ℕ) :=
  (bound A P)⁻¹ • (AsymptoticCylinderTerminal.projection Y).comp
    ((AsymptoticCylinder.inclusion P.epsilon_pos).comp (cylinderFinite A P hS hN δ e m))

def regularScaled (δ Y : ℝ) (e : Sector N) (z : UpperHalfPlane) :=
  (bound A P)⁻¹ • (AsymptoticRegularHeightCutoff.projection Y z).comp
    ((AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp (regularFinite A P hS hN δ e z))

theorem physicalScaled_norm (δ Y : ℝ) (e : Sector N) (m : ℕ) :
    ‖physicalScaled A P hS hN δ Y e m‖≤1 := by
  apply scaled_norm_le_one _ (zero_lt_one.trans_le (bound_one_le A P))
  exact (contract_left _ _ (AsymptoticCylinderTerminal.projection_norm_le Y)).trans
    ((contract_left _ _ (AsymptoticCylinder.inclusion_norm_le P.epsilon_pos)).trans
      (cylinderFinite_norm A P hS hN δ e m))

theorem regularScaled_norm (δ Y : ℝ) (e : Sector N) (z : UpperHalfPlane) :
    ‖regularScaled A P hS hN δ Y e z‖≤1 := by
  apply scaled_norm_le_one _ (zero_lt_one.trans_le (bound_one_le A P))
  exact (contract_left _ _ (AsymptoticRegularHeightCutoff.projection_norm_le Y z)).trans
    ((contract_left _ _ (AsymptoticRegularInclusion.inclusion_norm_le P.epsilon_pos z)).trans
      (regularFinite_norm A P hS hN δ e z))

theorem physicalScaled_error {δ Y : ℝ} (hδ : 0<δ) (hY : 0≤Y) (e : Sector N) (m : ℕ) :
    ‖physicalScaled A P hS hN δ Y e m-
      QuantitativeArithmeticRetainedCylinderNormalization.scaled A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m‖≤approximationError A P δ Y := by
  apply scaled_difference_norm_le _ _ (inv_nonneg.mpr (zero_le_one.trans (bound_one_le A P)))
    (inv_le_one_of_one_le₀ (bound_one_le A P))
  exact cut_error _ _ _ _ (AsymptoticCylinder.inclusion_norm_le P.epsilon_pos)
    (AsymptoticCylinderTerminal.projection_norm_le Y)
    (AsymptoticCylinderTerminal.inclusion_cut_error P.epsilon_pos hY)
    (div_nonneg hY P.epsilon_pos.le)
    (QuantitativeArithmeticRetainedCylinderExtension.extension_norm_le A hS hN P
      (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
      (fun p _ => ramifiedParameter_norm e p) (by omega) m (physical_contraction A P hS hN e m))
    (cylinderFinite_error A P hS hN hδ e m)

theorem regularScaled_error {δ Y : ℝ} (hδ : 0<δ) (hY : 0≤Y) (e : Sector N) (z : UpperHalfPlane) :
    ‖regularScaled A P hS hN δ Y e z-
      QuantitativeArithmeticRetainedRegularNormalization.scaled A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) z‖≤approximationError A P δ Y := by
  apply scaled_difference_norm_le _ _ (inv_nonneg.mpr (zero_le_one.trans (bound_one_le A P)))
    (inv_le_one_of_one_le₀ (bound_one_le A P))
  exact cut_error _ _ _ _ (AsymptoticRegularInclusion.inclusion_norm_le P.epsilon_pos z)
    (AsymptoticRegularHeightCutoff.projection_norm_le Y z)
    (AsymptoticRegularHeightCutoff.inclusion_cut_error P.epsilon_pos hY z)
    (div_nonneg hY P.epsilon_pos.le)
    (QuantitativeArithmeticRetainedRegularExtension.extension_norm_le A hS hN P
      (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
      (fun p _ => ramifiedParameter_norm e p) (by omega) z (regular_contraction A P hS hN e z))
    (QuantitativeArithmeticRetainedFiniteSchedule.regular_error A P hS hN hδ e z)

/-- An explicit Newton-polynomial approximation to the original normalized
reconstruction, with the same error at every weight and orbit root. -/
def normalizedError (δ Y : ℝ) (n : ℕ) : ℝ :=
  approximationError A P δ Y*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
    (1-gramLower A P)^(2^n)/Real.sqrt (gramLower A P)

theorem physical_normalized_error {δ Y : ℝ} (hδ : 0<δ) (hY : 0≤Y) (e : Sector N) (m n : ℕ) :
    ‖polynomialNormalizedReconstruction (physicalScaled A P hS hN δ Y e m) n-
      QuantitativeArithmeticRetainedCylinderNormalization.normalized A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m‖≤normalizedError A P δ Y n :=
  finite_polynomial_normalization_closed_error _ _ (gramLower_pos A P) (gramLower_le_one A P)
    (QuantitativeArithmeticRetainedCylinderNormalization.scaled_bounds A hS hN P
      (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
      (fun p _ => ramifiedParameter_norm e p) (by omega) m (physical_contraction A P hS hN e m)).2
    (QuantitativeArithmeticRetainedCylinderNormalization.scaled_bounds A hS hN P
      (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
      (fun p _ => ramifiedParameter_norm e p) (by omega) m (physical_contraction A P hS hN e m)).1
    ((physicalScaled_norm A P hS hN δ Y e m).trans (by norm_num))
    (physicalScaled_error A P hS hN hδ hY e m) n

theorem regular_normalized_error {δ Y : ℝ} (hδ : 0<δ) (hY : 0≤Y) (e : Sector N)
    (z : UpperHalfPlane) (n : ℕ) :
    ‖polynomialNormalizedReconstruction (regularScaled A P hS hN δ Y e z) n-
      QuantitativeArithmeticRetainedRegularNormalization.normalized A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) z‖≤normalizedError A P δ Y n :=
  finite_polynomial_normalization_closed_error _ _ (gramLower_pos A P) (gramLower_le_one A P)
    (QuantitativeArithmeticRetainedRegularNormalization.scaled_bounds A hS hN P
      (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
      (fun p _ => ramifiedParameter_norm e p) (by omega) z (regular_contraction A P hS hN e z)).2
    (QuantitativeArithmeticRetainedRegularNormalization.scaled_bounds A hS hN P
      (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
      (fun p _ => ramifiedParameter_norm e p) (by omega) z (regular_contraction A P hS hN e z)).1
    ((regularScaled_norm A P hS hN δ Y e z).trans (by norm_num))
    (regularScaled_error A P hS hN hδ hY e z) n

/-- An explicit efficient Newton cutoff for the common positive Gram gap. -/
def newtonDepth (τ : ℝ) : ℕ :=
  QuantitativeHolomorphic.Schedule.binaryDepth
    (Real.log (4/(τ*Real.sqrt (gramLower A P)))/gramLower A P)

theorem newton_error {τ : ℝ} (hτ : 0<τ) :
    (1-gramLower A P)^(2^newtonDepth A P τ)/Real.sqrt (gramLower A P)≤τ/4 := by
  let c := gramLower A P
  have hc : 0<c := gramLower_pos A P
  have hc1 : c≤1 := gramLower_le_one A P
  have hs : 0<Real.sqrt c := Real.sqrt_pos.mpr hc
  let n := newtonDepth A P τ
  let R := 4/(τ*Real.sqrt c)
  have hR : 0<R := by dsimp only [R]; positivity
  have hp : Real.log R≤c*(2:ℝ)^n := by
    have hh := QuantitativeHolomorphic.Schedule.binaryDepth_lower (Real.log R/c)
    exact ((div_le_iff₀ hc).mp hh).trans_eq (mul_comm _ _)
  have hpow : (1-c)^(2^n)≤Real.exp (-(c*(2:ℝ)^n)) := by
    calc
      _ ≤ (Real.exp (-c))^(2^n) := pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg c) _
      _ = _ := by rw [←Real.exp_nat_mul]; push_cast; congr 1; ring
  have hexp : Real.exp (-(c*(2:ℝ)^n))≤1/R := by
    calc
      _ ≤ Real.exp (-Real.log R) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg,Real.exp_log hR,one_div]
  apply (div_le_div_of_nonneg_right (hpow.trans hexp) hs.le).trans_eq
  dsimp only [R]
  field_simp

def rawTolerance (τ : ℝ) : ℝ :=
  τ/(4*QuantitativeHolomorphic.Schedule.amplification (newtonDepth A P τ))

def lowerHeight (τ : ℝ) : ℝ := P.ε/bound A P*rawTolerance A P τ

theorem rawTolerance_pos {τ : ℝ} (hτ : 0<τ) : 0<rawTolerance A P τ := by
  unfold rawTolerance
  exact div_pos hτ (mul_pos (by norm_num) (QuantitativeHolomorphic.Schedule.amplification_pos _))

theorem lowerHeight_pos {τ : ℝ} (hτ : 0<τ) : 0<lowerHeight A P τ :=
  mul_pos (div_pos P.epsilon_pos (zero_lt_one.trans_le (bound_one_le A P))) (rawTolerance_pos A P hτ)

/-- One requested accuracy selects all four cutoffs explicitly. -/
theorem normalizedError_schedule {τ : ℝ} (hτ : 0<τ) :
    normalizedError A P (rawTolerance A P τ) (lowerHeight A P τ) (newtonDepth A P τ)≤τ := by
  have hB : bound A P≠0 := (zero_lt_one.trans_le (bound_one_le A P)).ne'
  have hC : QuantitativeHolomorphic.Schedule.amplification (newtonDepth A P τ)≠0 :=
    (QuantitativeHolomorphic.Schedule.amplification_pos _).ne'
  have he : approximationError A P (rawTolerance A P τ) (lowerHeight A P τ)*
      QuantitativeHolomorphic.Schedule.amplification (newtonDepth A P τ)=τ/2 := by
    unfold approximationError lowerHeight rawTolerance
    field_simp [hB,P.epsilon_pos.ne',hC]
    ring
  have hn := newton_error A P hτ
  unfold normalizedError
  change approximationError A P (rawTolerance A P τ) (lowerHeight A P τ)*
    (1+3*(3^newtonDepth A P τ:ℕ))*(7:ℝ)^(4^newtonDepth A P τ)+_≤τ
  have he' := he
  unfold QuantitativeHolomorphic.Schedule.amplification at he'
  nlinarith only [hn,he',hτ]

theorem scheduled_physical_error {τ : ℝ} (hτ : 0<τ) (e : Sector N) (m : ℕ) :
    ‖polynomialNormalizedReconstruction
      (physicalScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e m) (newtonDepth A P τ)-
      QuantitativeArithmeticRetainedCylinderNormalization.normalized A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m‖≤τ :=
  (physical_normalized_error A P hS hN (rawTolerance_pos A P hτ) (lowerHeight_pos A P hτ).le e m _).trans
    (normalizedError_schedule A P hτ)

theorem scheduled_regular_error {τ : ℝ} (hτ : 0<τ) (e : Sector N) (z : UpperHalfPlane) :
    ‖polynomialNormalizedReconstruction
      (regularScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e z) (newtonDepth A P τ)-
      QuantitativeArithmeticRetainedRegularNormalization.normalized A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) z‖≤τ :=
  (regular_normalized_error A P hS hN (rawTolerance_pos A P hτ) (lowerHeight_pos A P hτ).le e z _).trans
    (normalizedError_schedule A P hτ)

#print axioms normalizedError_schedule
#print axioms scheduled_physical_error
#print axioms scheduled_regular_error
#print axioms cylinderFinite_error
#print axioms physicalScaled_norm
#print axioms regularScaled_norm
#print axioms physicalScaled_error
#print axioms regularScaled_error
#print axioms physical_normalized_error
#print axioms regular_normalized_error
end QuantitativeArithmeticRetainedFiniteNormalization
