module

public import AsymptoticSharedFiniteTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticSharedApproximation

open UpperHalfPlane MeasureTheory Set Filter FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorSigns AsymptoticReconstructedCount AsymptoticRegularTrace
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The low-height cutoff, inverse degree, reconstruction depth and fold
set are chosen once for both representations. They approximate the
actual uncut positive traces uniformly over all weights and sectors. -/
theorem positive_traces_approximation (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {δ : ℝ} (hδ : 0<δ) :
    ∃ Y : ℝ,0<Y ∧ Y≤(parameters A P).ε ∧ ∃ n d : ℕ,∃ I : Finset ℤ,
      (∀ h : ℕ,∀ e : Sector N,
        ‖AsymptoticCylinderObservation.finiteCutPolynomialTrace A hN P r s hs h e Y n d I-
          AsymptoticCylinderObservation.holomorphicTrace A hN P r s hs h e‖/(2*h+2:ℕ)<δ) ∧
      (∀ e : Sector N,
        ‖signedTrace volume (AsymptoticRegularObservation.finiteCutPolynomialTerminal A hN P r s hs e Y n d I)-
          (trace volume (AsymptoticRegularObservation.positive A hN P r s hs e)).toReal‖<δ) := by
  let ε := (parameters A P).ε
  have hε : 0<ε := (parameters A P).epsilon_pos
  let Y : ℕ → ℝ := fun j => ε/((j:ℝ)+1)
  have hYpos (j : ℕ) : 0<Y j := div_pos hε (by positivity)
  have hYε (j : ℕ) : Y j≤(parameters A P).ε := by
    apply (div_le_iff₀ (by positivity : 0<(j:ℝ)+1)).mpr
    have hj : (0:ℝ)≤j := Nat.cast_nonneg j
    change ε≤ε*((j:ℝ)+1)
    nlinarith
  have hY : Tendsto Y atTop (𝓝 0) := by
    simpa only [Y,div_eq_mul_inv,one_div,one_mul,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul ε
  have hh := AsymptoticCylinderObservation.cutHolomorphicTrace_tendstoUniformly A hN P r s hs Y
    (fun j => (hYpos j).le) hYε hY
  have hr := AsymptoticRegularObservation.cutPositive_trace_tendstoUniformly A hN P r s hs Y
    (fun j => (hYpos j).le) hYε hY
  obtain ⟨j,hjH,hjR⟩ := (((Metric.tendstoUniformly_iff.mp hh) (δ/2) (half_pos hδ)).and
    ((Metric.tendstoUniformly_iff.mp hr) (δ/2) (half_pos hδ))).exists
  obtain ⟨n,d,I,hnH,hnR⟩ := cutoff_positive_traces_approximation A hN P r s hs (Y j) (hYε j) (half_pos hδ)
  refine ⟨Y j,hYpos j,hYε j,n,d,I,?_,?_⟩
  · intro h e
    have hk : (0:ℝ)<(2*h+2:ℕ) := by positivity
    have hp : ‖AsymptoticCylinderObservation.cutHolomorphicTrace A hN P r s hs h e (Y j) (hYε j)-
        AsymptoticCylinderObservation.holomorphicTrace A hN P r s hs h e‖/(2*h+2:ℕ)<δ/2 := by
      simpa only [dist_eq_norm,← sub_div,norm_div,Real.norm_of_nonneg hk.le,norm_sub_rev] using hjH (h,e)
    have ht := div_le_div_of_nonneg_right (norm_sub_le_norm_sub_add_norm_sub
      (AsymptoticCylinderObservation.finiteCutPolynomialTrace A hN P r s hs h e (Y j) n d I)
      (AsymptoticCylinderObservation.cutHolomorphicTrace A hN P r s hs h e (Y j) (hYε j))
      (AsymptoticCylinderObservation.holomorphicTrace A hN P r s hs h e)) hk.le
    rw [add_div] at ht
    exact ht.trans_lt ((add_lt_add (hnH h e) hp).trans_eq (add_halves δ))
  · intro e
    have hp : ‖(trace volume (AsymptoticRegularObservation.cutPositive A hN P r s hs e (Y j))).toReal-
        (trace volume (AsymptoticRegularObservation.positive A hN P r s hs e)).toReal‖<δ/2 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hjR e
    exact (norm_sub_le_norm_sub_add_norm_sub _
      (trace volume (AsymptoticRegularObservation.cutPositive A hN P r s hs e (Y j))).toReal _).trans_lt
      ((add_lt_add (hnR e) hp).trans_eq (add_halves δ))

/-- Reduction of the actual fixed-observation large-weight limit to
the finite branch-word calculation. That calculation remains an explicit
premise here; this theorem does not assert the asymptotic Euler count. -/
theorem holomorphic_trace_limit_of_finite_words (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (hfinite : ∀ Y : ℝ,0<Y → Y≤(parameters A P).ε → ∀ n d : ℕ,∀ I : Finset ℤ,∀ e : Sector N,
      Tendsto
        (fun h : ℕ => AsymptoticCylinderObservation.finiteCutPolynomialTrace A hN P r s hs h e Y n d I/(2*h+2:ℕ))
        atTop (𝓝 (signedTrace volume
          (AsymptoticRegularObservation.finiteCutPolynomialTerminal A hN P r s hs e Y n d I)/(4*Real.pi))))
    (e : Sector N) :
    Tendsto (fun h : ℕ => AsymptoticCylinderObservation.holomorphicTrace A hN P r s hs h e/(2*h+2:ℕ))
      atTop (𝓝 ((trace volume (AsymptoticRegularObservation.positive A hN P r s hs e)).toReal/(4*Real.pi))) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hδ3 : 0<δ/3 := by positivity
  obtain ⟨Y,hY0,hY,n,d,I,hH,hR⟩ := positive_traces_approximation A hN P r s hs hδ3
  have hπ : (1:ℝ)≤4*Real.pi := by nlinarith [Real.two_le_pi]
  have hπ0 : 0<4*Real.pi := by positivity
  let B := signedTrace volume (AsymptoticRegularObservation.finiteCutPolynomialTerminal A hN P r s hs e Y n d I)
  let T := (trace volume (AsymptoticRegularObservation.positive A hN P r s hs e)).toReal
  have hBT : ‖B/(4*Real.pi)-T/(4*Real.pi)‖<δ/3 := by
    rw [← sub_div,norm_div,Real.norm_of_nonneg hπ0.le]
    have hb : ‖B-T‖/(4*Real.pi)≤‖B-T‖ := by
      apply (div_le_iff₀ hπ0).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hπ (norm_nonneg (B-T))
    exact hb.trans_lt (hR e)
  have ht := (Metric.tendsto_nhds.mp (hfinite Y hY0 hY n d I e)) (δ/3) hδ3
  apply ht.mono
  intro h hh
  let F := AsymptoticCylinderObservation.finiteCutPolynomialTrace A hN P r s hs h e Y n d I/(2*h+2:ℕ)
  let H := AsymptoticCylinderObservation.holomorphicTrace A hN P r s hs h e/(2*h+2:ℕ)
  have hk : (0:ℝ)<(2*h+2:ℕ) := by positivity
  have hHF : ‖H-F‖<δ/3 := by
    rw [norm_sub_rev]
    simpa only [H,F,← sub_div,norm_div,Real.norm_of_nonneg hk.le] using hH h e
  have hFB : ‖F-B/(4*Real.pi)‖<δ/3 := by simpa only [dist_eq_norm] using hh
  change dist H (T/(4*Real.pi))<δ
  rw [dist_eq_norm]
  have ha := norm_sub_le_norm_sub_add_norm_sub H F (T/(4*Real.pi))
  have hb := norm_sub_le_norm_sub_add_norm_sub F (B/(4*Real.pi)) (T/(4*Real.pi))
  linarith

#print axioms positive_traces_approximation
#print axioms holomorphic_trace_limit_of_finite_words

end AsymptoticSharedApproximation
