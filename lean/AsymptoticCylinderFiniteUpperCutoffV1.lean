module

public import AsymptoticCylinderUpperCutoffLimitV1
public import AsymptoticCylinderFinitePolynomialV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderObservation

open UpperHalfPlane Set ContinuousLinearMap Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation AsymptoticReconstructedCount AsymptoticCoerciveNeumann
open AsymptoticDiagonalTrace AsymptoticFourierNorm
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem finiteCutInversePolynomial_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) :
    ‖finiteCutInversePolynomial A hN P r s hs h e Y n d I‖ ≤
      polynomialBound (AsymptoticSharedApproximation.normalBound A hN P r s hs)
        (normalBound A hN P r s hs) n :=
  polynomial_norm_le_of_bound _ _ (finiteCutNormal_norm_le A hN P r s hs h e Y d I) n

noncomputable def finiteUpperCutPolynomialTrace (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y H : ℝ)
    (n d : ℕ) (I : Finset ℤ) : ℝ :=
  upperCutTrace (finiteCutReconstruction A hN P h e Y d I)
    (finiteCutInversePolynomial A hN P r s hs h e Y n d I)
    (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos H

/-- The actual finite holomorphic polynomial traces permit removal of the
upper cusp, uniformly in sectors and all finite reconstruction parameters.
The polynomial degree is fixed before choosing the height cutoff. -/
theorem finiteUpperCutPolynomialTrace_approximation (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ H₀ : ℝ, 0<H₀ ∧ ∀ H : ℝ, H₀≤H → ∀ᶠ h : ℕ in atTop,
      ∀ e : Sector N, ∀ Y : ℝ, ∀ d : ℕ, ∀ I : Finset ℤ,
        ‖finiteCutPolynomialTrace A hN P r s hs h e Y n d I-
          finiteUpperCutPolynomialTrace A hN P r s hs h e Y H n d I‖/(2*h+2:ℕ)<δ := by
  have hw : Tendsto (fun h : ℕ => 2*h) atTop atTop :=
    tendsto_atTop_mono (fun h => by change h ≤ 2*h; omega) tendsto_id
  obtain ⟨H₀,hH₀,hh⟩ := factored_upperCut_trace_small (σ := Sector N × ℝ × ℕ × Finset ℤ)
    (fun h => 2*h) hw
    (fun h p => finiteCutBaseReconstruction A hN P h p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun h p => finiteCutInversePolynomial A hN P r s hs h p.1 p.2.1 n p.2.2.1 p.2.2.2)
    (fun h p => finiteCutBaseReconstruction_norm_le A hN P h p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun h p => finiteCutInversePolynomial_norm_le A hN P r s hs h p.1 p.2.1 n p.2.2.1 p.2.2.2)
    ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos hδ
  refine ⟨H₀,hH₀,?_⟩
  intro H hH
  filter_upwards [hh H hH] with h ha
  intro e Y d I
  exact ha (e,Y,d,I)

#print axioms finiteCutInversePolynomial_norm_le
#print axioms finiteUpperCutPolynomialTrace_approximation

end AsymptoticCylinderObservation
