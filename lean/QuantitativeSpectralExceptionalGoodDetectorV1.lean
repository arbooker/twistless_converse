module

public import QuantitativeSpectralExceptionalGoodRootV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGoodRoot

open UpperHalfPlane MeasureTheory AsymptoticRegularTrace QuantitativeSpectralObservability
open QuantitativeSpectralCornerCutRow
open scoped lp ENNReal

/-- The actual low-residual trace detector only needs observability and
range inclusion on the proved invariant conull set of good roots. Source
compression discharges the everywhere hypotheses of the existing detector. -/
theorem observable_low_trace_good (N : ℕ) (hN : 0<N)
    (P V : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (P x)] [∀ x, CompleteSpace (V x)]
    (hmP : ∀ g h, Measurable (fun x => matrix (P x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection))
    (B C : ℍ → Space →L[ℂ] Space)
    (hmB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
    (hmC : ∀ g h, Measurable (fun x => matrix (C x) g h)) (hcC : Covariant C)
    (MB MC : ℝ) (hMB : ∀ x, ‖B x‖≤MB) (hMC : ∀ x, ‖C x‖≤MC)
    {c K : ℝ} (hc : 0<c) (hK : 0≤K) (hsmall : K*c^2<1)
    (hobs : ∀ x, fundamentalGood N x → ∀ v∈P x,
      ‖v‖^2≤K*(‖B x v‖^2+‖C x v‖^2))
    (hmap : ∀ x, fundamentalGood N x → ∀ v∈P x, C x v∈V x) :
    trace volume (fun x => (nextSpace (P x) (B x) c).starProjection)≤
      trace volume (fun x => (V x).starProjection) := by
  have hrP := family_regular N hN (fun x => (P x).starProjection) hmP hcP
  have hrB := family_regular N hN B hmB hcB
  have hrC := family_regular N hN C hmC hcC
  have hmP' : ∀ g h, Measurable (fun x => matrix (source N P x).starProjection g h) := by
    simp only [source_projection]
    exact hrP.1
  have hcP' : Covariant (fun x => (source N P x).starProjection) := by
    simp only [source_projection]
    exact hrP.2
  have hh := observable_low_trace volume AsymptoticRationalGroup.measurePreserving
    (source N P) (source N V) hmP' hcP' (family N B) (family N C)
    hrB.1 hrB.2 hrC.1 hrC.2 MB MC (family_norm N B hMB) (family_norm N C hMC)
    hc hK hsmall (source_observability N P B C K hobs) (source_map N P V C hmap)
  rw [source_trace N hN V] at hh
  have he : trace volume (fun x => (nextSpace (source N P x) (family N B x) c).starProjection)=
      trace volume (fun x => (nextSpace (P x) (B x) c).starProjection) := by
    unfold trace
    apply lintegral_congr_ae
    filter_upwards [fundamentalGood_ae N hN] with x hx
    simp only [source,family,ite_eq_left hx]
  rwa [he] at hh

#print axioms observable_low_trace_good

end QuantitativeSpectralExceptionalGoodRoot
