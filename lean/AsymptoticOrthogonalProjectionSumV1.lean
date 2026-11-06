module

public import AsymptoticProjectionTraceV1
public import Mathlib.Analysis.InnerProductSpace.Subspace

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public section

namespace AsymptoticOrthogonalProjectionSum

open ContinuousLinearMap InnerProductSpace MeasureTheory
open scoped InnerProduct ENNReal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [Fintype ι]

/-- Bessel's inequality for a finite orthogonal family of closed
subspaces, without any finite-dimensionality assumption. -/
theorem sum_projection_norm_sq_le (V : ι → Submodule ℂ E) [∀ i,CompleteSpace (V i)]
    (ho : ∀ i j,i≠j → V i≤(V j)ᗮ) (x : E) :
    (∑ i,‖(V i).starProjection x‖^2)≤‖x‖^2 := by
  classical
  have hfamily : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ) := by
    intro i j hij v w
    exact ho j i hij.symm w.property v v.property
  have hn := hfamily.norm_sum (fun i => (V i).orthogonalProjectionOnto x) Finset.univ
  change ‖∑ i,(V i).starProjection x‖^2=∑ i,‖(V i).starProjection x‖^2 at hn
  have hi (i : ι) : (⟪x,(V i).starProjection x⟫_ℂ).re=‖(V i).starProjection x‖^2 := by
    change RCLike.re (⟪x,(V i).starProjection x⟫_ℂ)=_
    rw [inner_re_symm]
    exact (V i).re_inner_starProjection_eq_normSq x
  have hh : (⟪x,∑ i,(V i).starProjection x⟫_ℂ).re=∑ i,‖(V i).starProjection x‖^2 := by
    rw [inner_sum]
    change Complex.reCLM (∑ i,⟪x,(V i).starProjection x⟫_ℂ)=_
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => hi i)
  have he := norm_sub_sq (𝕜:=ℂ) x (∑ i,(V i).starProjection x)
  change ‖x-∑ i,(V i).starProjection x‖^2=
    ‖x‖^2-2*(⟪x,∑ i,(V i).starProjection x⟫_ℂ).re+‖∑ i,(V i).starProjection x‖^2 at he
  rw [hh,hn] at he
  nlinarith [sq_nonneg ‖x-∑ i,(V i).starProjection x‖]

theorem sum_projection_norm_sq_le_common (V : ι → Submodule ℂ E) [∀ i,CompleteSpace (V i)]
    (ho : ∀ i j,i≠j → V i≤(V j)ᗮ)
    (U : Submodule ℂ E) [CompleteSpace U] (hVU : ∀ i,V i≤U) (x : E) :
    (∑ i,‖(V i).starProjection x‖^2)≤‖U.starProjection x‖^2 := by
  have h := sum_projection_norm_sq_le V ho (U.starProjection x)
  have he (i : ι) : (V i).starProjection (U.starProjection x)=(V i).starProjection x :=
    congrArg (fun T : E →L[ℂ] E => T x) (Submodule.starProjection_comp_starProjection_of_le (hVU i))
  simpa only [he] using h

/-- Superadditivity of the lower integral is sufficient for the upper
trace bound; no extra measurability assumption on a sector projection
is needed for this direction. -/
theorem sum_lintegral_le {α κ : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset κ) (f : κ → α → ℝ≥0∞) :
    (∑ i∈s,∫⁻ x,f i x ∂μ)≤∫⁻ x,∑ i∈s,f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,lintegral_zero,le_refl]
  | insert i s his ih =>
    simp_rw [Finset.sum_insert his]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add (f i) (fun x => ∑ j∈s,f j x))

#print axioms sum_projection_norm_sq_le
#print axioms sum_projection_norm_sq_le_common
#print axioms sum_lintegral_le

end AsymptoticOrthogonalProjectionSum

namespace AsymptoticRegularTrace

open MeasureTheory AsymptoticOrthogonalProjectionSum
open scoped lp ENNReal

variable {G α ι : Type*} [Group G] [MeasurableSpace α] [Fintype ι]

/-- Sum the actual orthogonal sector traces before comparing with one
common ambient corner. -/
theorem sum_projection_trace_le (μ : Measure α)
    (V : ι → α → Submodule ℂ ℓ²(G,ℂ)) [∀ i x,CompleteSpace (V i x)]
    (ho : ∀ x i j,i≠j → V i x≤(V j x)ᗮ)
    (U : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)]
    (hVU : ∀ i x,V i x≤U x) :
    (∑ i,trace μ (fun x => (V i x).starProjection))≤trace μ (fun x => (U x).starProjection) := by
  classical
  simp only [trace,projection_root_eq_norm]
  apply (sum_lintegral_le μ Finset.univ (fun i x => ENNReal.ofReal (‖(V i x).starProjection (delta 1)‖^2))).trans
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ENNReal.ofReal_sum_of_nonneg (s:=Finset.univ) (fun i _ => sq_nonneg ‖(V i x).starProjection (delta 1)‖)]
  exact ENNReal.ofReal_le_ofReal
    (sum_projection_norm_sq_le_common (fun i => V i x) (ho x) (U x) (fun i => hVU i x) (delta 1))

theorem sum_projection_trace_toReal_le (μ : Measure α)
    (V : ι → α → Submodule ℂ ℓ²(G,ℂ)) [∀ i x,CompleteSpace (V i x)]
    (ho : ∀ x i j,i≠j → V i x≤(V j x)ᗮ)
    (U : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)]
    (hVU : ∀ i x,V i x≤U x) (hf : trace μ (fun x => (U x).starProjection)<∞) :
    (∑ i,(trace μ (fun x => (V i x).starProjection)).toReal)≤
      (trace μ (fun x => (U x).starProjection)).toReal := by
  have hi (i : ι) : trace μ (fun x => (V i x).starProjection)≠∞ :=
    (projection_trace_finite_of_le μ (V i) U (hVU i) hf).ne
  rw [← ENNReal.toReal_sum (fun i _ => hi i)]
  exact ENNReal.toReal_mono hf.ne (sum_projection_trace_le μ V ho U hVU)

#print axioms sum_projection_trace_le
#print axioms sum_projection_trace_toReal_le

end AsymptoticRegularTrace
