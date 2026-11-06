module

public import AsymptoticCylinderCutTraceV1
public import AsymptoticObservationPerturbationV1
public import AsymptoticCompactObservationCountV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstructedCount

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)
variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- Quantitative cutoff error for the actual cylinder observation
operator. The coefficient is uniform in weight and sector. -/
theorem cut_operator_error (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY0 : 0≤Y) (hY : Y≤(parameters A P).ε) (L : Space →L[ℂ] J)
    (BL : ℝ) (hL : ‖L‖≤BL) :
    let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P)
    ‖operator (includedReconstruction A hN P h e) L (terminal_lower_bound A hN P h e)-
      operator (cutReconstruction A hN P h e Y) L (cutReconstruction_norm_ge A hN P h e Y hY)‖≤
        (BR+BR)*(1+BR*BR*(1+BL^2))*(Y/(parameters A P).ε*BR) := by
  dsimp only
  have hr := includedReconstruction_norm_le A hN P h e
  have hs := cutReconstruction_norm_le A hN P h e Y
  have hBR := (norm_nonneg (includedReconstruction A hN P h e)).trans hr
  have hBL := (norm_nonneg L).trans hL
  apply (operator_sub_norm_le _ _ L (terminal_lower_bound A hN P h e)
    (cutReconstruction_norm_ge A hN P h e Y hY)).trans
  gcongr <;> first
    | exact hr
    | exact hs
    | exact hL
    | exact cutReconstruction_error A hN P h e Y hY0

#print axioms cut_operator_error

end AsymptoticReconstructedCount

namespace AsymptoticCylinderObservation

open UpperHalfPlane Set ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCylinder AsymptoticObservation AsymptoticSectorSigns
open AsymptoticCompactObservationCount (Row)
open AsymptoticReconstructedCount

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def observationsBound (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => AsymptoticHyperbolicSlash.Space)).symm.toContinuousLinearMap‖*
    ∑ i,AsymptoticCompactObservationCount.rowBound hN (r i) (hs i) (parameters A P).epsilon_pos ((parameters A P).s+4)

noncomputable def positive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) : Space →L[ℂ] Space :=
  operator (includedReconstruction A hN P h e)
    (AsymptoticCompactObservationCount.observations hN r s hs (parameters A P).epsilon_pos
      ((parameters A P).s+4) (h+1) e) (terminal_lower_bound A hN P h e)

noncomputable def cutPositive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) : Space →L[ℂ] Space :=
  operator (cutReconstruction A hN P h e Y)
    (AsymptoticCompactObservationCount.observations hN r s hs (parameters A P).epsilon_pos
      ((parameters A P).s+4) (h+1) e) (cutReconstruction_norm_ge A hN P h e Y hY)

theorem cutPositive_isPositive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) :
    (cutPositive A hN P r s hs h e Y hY).IsPositive := operator_positive _ _ _

theorem cutPositive_norm_le_one (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) :
    ‖cutPositive A hN P r s hs h e Y hY‖≤1 := operator_norm_le_one _ _ _

noncomputable def cutErrorBound (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ) : ℝ :=
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P)
  (BR+BR)*(1+BR*BR*(1+(observationsBound A hN P r s hs)^2))*(Y/(parameters A P).ε*BR)

theorem cutPositive_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY0 : 0≤Y) (hY : Y≤(parameters A P).ε) :
    ‖positive A hN P r s hs h e-cutPositive A hN P r s hs h e Y hY‖≤cutErrorBound A hN P r s hs Y :=
  cut_operator_error A hN P h e Y hY0 hY _ (observationsBound A hN P r s hs)
    (AsymptoticCompactObservationCount.observations_norm_le hN r s hs (parameters A P).epsilon_pos
      ((parameters A P).s+4) (h+1) e)

#print axioms cutPositive_isPositive
#print axioms cutPositive_norm_le_one
#print axioms cutPositive_error

end AsymptoticCylinderObservation
