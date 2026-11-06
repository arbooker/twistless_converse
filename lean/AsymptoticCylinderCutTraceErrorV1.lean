module

public import AsymptoticCylinderCutLimitV1
public import AsymptoticFourierTraceContinuityV1
public import AsymptoticHolomorphicPerturbationV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderObservation

open UpperHalfPlane Set ContinuousLinearMap InnerProductSpace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation AsymptoticReconstructedCount
open AsymptoticFourierNorm AsymptoticDiagonalTrace
open AsymptoticCompactObservationCount (Row)
open scoped InnerProduct

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def holomorphicTrace (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) : ℝ :=
  let U := holomorphicSpace (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos
  trace (fourierBasis (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos)
    (U.subtypeL.adjoint.comp ((positive A hN P r s hs h e).comp U.subtypeL))

noncomputable def cutHolomorphicTrace (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) : ℝ :=
  let U := holomorphicSpace (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos
  trace (fourierBasis (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos)
    (U.subtypeL.adjoint.comp ((cutPositive A hN P r s hs h e Y hY).comp U.subtypeL))

/-- The common Fourier tail constant is independent of the weight,
sector, cutoff height and compact observation family. -/
noncomputable def traceTailConstant (P : Parameters A) : ℝ :=
  2*(1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P))^2*
    majorantConstant ((parameters A P).s+4) (4*Real.pi) (parameters A P).ε

theorem traceTailConstant_nonneg (P : Parameters A) : 0≤traceTailConstant A P := by
  unfold traceTailConstant majorantConstant
  positivity

/-- The actual cutoff and uncut holomorphic traces satisfy the Fourier
head/tail estimate, with their summability established from the majorant. -/
theorem cutHolomorphicTrace_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY0 : 0≤Y) (hY : Y≤(parameters A P).ε) (M : ℕ) (hM : 0<M) :
    ‖holomorphicTrace A hN P r s hs h e-cutHolomorphicTrace A hN P r s hs h e Y hY‖≤
      (M:ℝ)*cutErrorBound A hN P r s hs Y+traceTailConstant A P*(2*h+2:ℕ)^2/(M:ℝ) := by
  let P' := parameters A P
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A P'
  let R := includedReconstruction A hN P h e
  let S := cutReconstruction A hN P h e Y
  let L := AsymptoticCompactObservationCount.observations hN r s hs P'.epsilon_pos (P'.s+4) (h+1) e
  let U := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
  let b := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
  let Q₀ := holomorphicOperator R L (terminal_lower_bound A hN P h e) U
  let QY := holomorphicOperator S L (cutReconstruction_norm_ge A hN P h e Y hY) U
  have hd : ‖Q₀-QY‖≤cutErrorBound A hN P r s hs Y :=
    (holomorphicOperator_sub_norm_le R S L _ _ U).trans (cutPositive_error A hN P r s hs h e Y hY0 hY)
  have hgram (n : ℕ) : ‖R.adjoint ((b n:U):Space)‖^2≤BR^2*modeRatio (2*h) (P'.s+4) (4*Real.pi) P'.ε (n+1) := by
    apply (reconstructed_fourier_gram (reconstruction A hN P h e) (2*h) (P'.s+4)
      (by positivity : 0<4*Real.pi) P'.epsilon_pos n).trans
    apply mul_le_mul_of_nonneg_right _ (modeRatio_nonneg _ _ _ _ P'.epsilon_pos)
    exact pow_le_pow_left₀ (norm_nonneg _) (reconstruction_norm_le A hN P h e) 2
  have hq (n : ℕ) : (⟪Q₀ (b n),b n⟫_ℂ).re≤BR^2*modeRatio (2*h) (P'.s+4) (4*Real.pi) P'.ε (n+1) := by
    have hi : (⟪Q₀ (b n),b n⟫_ℂ).re=
        (⟪operator R L (terminal_lower_bound A hN P h e) ((b n:U):Space),((b n:U):Space)⟫_ℂ).re :=
      congrArg Complex.re (holomorphicOperator_inner R L (terminal_lower_bound A hN P h e) U (b n))
    rw [hi]
    exact (operator_re_inner_le_gram R L _ _).trans (hgram n)
  have hy (n : ℕ) : (⟪QY (b n),b n⟫_ℂ).re≤BR^2*modeRatio (2*h) (P'.s+4) (4*Real.pi) P'.ε (n+1) := by
    have hi : (⟪QY (b n),b n⟫_ℂ).re=
        (⟪operator S L (cutReconstruction_norm_ge A hN P h e Y hY) ((b n:U):Space),((b n:U):Space)⟫_ℂ).re :=
      congrArg Complex.re (holomorphicOperator_inner S L (cutReconstruction_norm_ge A hN P h e Y hY) U (b n))
    rw [hi]
    exact (operator_re_inner_le_gram S L _ _).trans
      (cutReconstruction_fourier_gram A hN P h e Y (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) n)
  exact trace_sub_le_fourier_cutoff b Q₀ QY (holomorphicOperator_positive R L _ U)
    (holomorphicOperator_positive S L _ U) (2*h) (P'.s+4) M hM
    (by positivity : 0<4*Real.pi) P'.epsilon_pos (sq_nonneg BR) hd hq hy

/-- With M=Bk, the normalized error is B times the norm error plus C/B.
All constants here have been supplied by the concrete cylinder operators. -/
theorem cutHolomorphicTrace_normalized_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY0 : 0≤Y) (hY : Y≤(parameters A P).ε) (B : ℕ) (hB : 0<B) :
    ‖holomorphicTrace A hN P r s hs h e-cutHolomorphicTrace A hN P r s hs h e Y hY‖/(2*h+2:ℕ)≤
      (B:ℝ)*cutErrorBound A hN P r s hs Y+traceTailConstant A P/(B:ℝ) := by
  have hk : (0:ℝ)<(2*h+2:ℕ) := by positivity
  have hBr : (0:ℝ)<B := by exact_mod_cast hB
  apply (div_le_iff₀ hk).mpr
  have he := cutHolomorphicTrace_error A hN P r s hs h e Y hY0 hY (B*(2*h+2)) (Nat.mul_pos hB (by omega))
  have hc : (B*(2*h+2):ℕ)*cutErrorBound A hN P r s hs Y+
      traceTailConstant A P*(2*h+2:ℕ)^2/(B*(2*h+2):ℕ)=
      ((B:ℝ)*cutErrorBound A hN P r s hs Y+traceTailConstant A P/(B:ℝ))*(2*h+2:ℕ) := by
    push_cast
    field_simp
  rwa [hc] at he

#print axioms traceTailConstant_nonneg
#print axioms cutHolomorphicTrace_error
#print axioms cutHolomorphicTrace_normalized_error

end AsymptoticCylinderObservation
