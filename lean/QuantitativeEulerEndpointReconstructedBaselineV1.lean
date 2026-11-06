module

public import QuantitativeEulerEndpointReconstructedFiniteV1
public import QuantitativeEulerEndpointNewBaselineRegularV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularReconstruction AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup MeasureTheory
open QuantitativeSpectralCornerCutRow QuantitativeSpectralRegularCornerStep

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ)
variable (P : Parameters A) (e : Sector N)
variable (F : UpperHalfPlane → Submodule ℂ RegularSpace) [∀ z, CompleteSpace (F z)]
variable (hF : ∀ z,F z≤TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)
variable {s : Set UpperHalfPlane} (hs : IsCompact s)

def reconstructedBaseline (a : ℝ) (z : UpperHalfPlane) : Submodule ℂ RegularSpace :=
  nextSpace (reconstructedImage A (NeZero.pos N) P e F hF z)
    (newBaselineDetector N e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z) (Real.sqrt a)

instance reconstructedBaseline_complete (a : ℝ) (z : UpperHalfPlane) :
    CompleteSpace (reconstructedBaseline A P e F hF hs a z) := by
  unfold reconstructedBaseline
  infer_instance

theorem reconstructed_baseline_le (a : ℝ) (z : UpperHalfPlane) :
    reconstructedBaseline A P e F hF hs a z ≤ reconstructedImage A (NeZero.pos N) P e F hF z :=
  nextSpace_le _ _ _

/-- The required baseline energy input is supplied by an actual spectral cut
on reconstructed vectors, with no truncation below the terminal height. -/
theorem reconstructed_baseline_energy (a : ℝ) (ha : 0≤a) (z : UpperHalfPlane)
    (v : RegularSpace) (hv : v∈reconstructedBaseline A P e F hF hs a z) :
    ‖newBaselineDetector N e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z v‖^2 ≤ a*‖v‖^2 := by
  simpa only [Real.sq_sqrt ha] using nextSpace_energy _ _ (Real.sqrt a) v hv

theorem reconstructed_baseline_regular
    (hmF : ∀ g k,Measurable (fun z => matrix (F z).starProjection g k))
    (hcF : Covariant (fun z => (F z).starProjection)) (a : ℝ) (ha : 0<a) :
    (∀ g k,Measurable (fun z => matrix (reconstructedBaseline A P e F hF hs a z).starProjection g k)) ∧
      Covariant (fun z => (reconstructedBaseline A P e F hF hs a z).starProjection) := by
  have hreg := reconstructed_image_regular A (NeZero.pos N) P e F hF hmF hcF
  obtain ⟨M,_hM,hM,hm,hc⟩ := newBaselineDetector_regular N e hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4)
  exact (step_regular _ _ hreg.1 hreg.2 hm hc M hM (Real.sqrt a) (Real.sqrt_pos.mpr ha)).1

theorem reconstructed_baseline_supported (q : ℕ) [Fact q.Prime]
    (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (hqfixed : ∀ b : QuantitativeArithmetic.UnitResidue N,
      ¬q∣(QuantitativeEulerDensityGenerators.primeLift N b).q)
    (hsF : ∀ z,Supported (integralGroup q) (F z).starProjection)
    (a : ℝ) (ha : 0<a) (z : UpperHalfPlane) :
    Supported (integralGroup q) (reconstructedBaseline A P e F hF hs a z).starProjection := by
  exact (step_supported _ _ _
    (reconstructed_image_supported A (NeZero.pos N) P e F hF q hqN hqQ hsF z)
    (newBaselineDetector_supported N e q hqN hqfixed hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z)
    (Real.sqrt a) (Real.sqrt_pos.mpr ha)).1

theorem reconstructed_baseline_kernel_survives (a : ℝ) (z : UpperHalfPlane)
    (v : RegularSpace) (hv : v∈reconstructedImage A (NeZero.pos N) P e F hF z)
    (hz : newBaselineDetector N e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z v=0) :
    v∈reconstructedBaseline A P e F hF hs a z :=
  kernel_survives _ _ _ hv hz

#print axioms reconstructed_baseline_energy
#print axioms reconstructed_baseline_regular
#print axioms reconstructed_baseline_supported
#print axioms reconstructed_baseline_kernel_survives
end QuantitativeEulerEndpointPrepared
