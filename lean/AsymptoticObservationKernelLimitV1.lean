module

public import AsymptoticObservationAmplificationV1
public import AsymptoticStrongConvergenceSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace Filter
open scoped InnerProduct Topology

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

def survivingSpace (R : G →L[ℂ] H) (L : H →L[ℂ] J) : Submodule ℂ H := R.range⊓L.ker

omit [CompleteSpace H] [CompleteSpace J] in
theorem survivingSpace_closed (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) : IsClosed (survivingSpace R L : Set H) :=
  (reconstruction_range_closed R hR).inter L.isClosed_ker

noncomputable def kernelProjection (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) : H →L[ℂ] H :=
  let : CompleteSpace (survivingSpace R L) := (survivingSpace_closed R L hR).completeSpace_coe
  (survivingSpace R L).starProjection

omit [CompleteSpace J] in
theorem kernelProjection_norm_le (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) : ‖kernelProjection R L hR‖≤1 := by
  let : CompleteSpace (survivingSpace R L) := (survivingSpace_closed R L hR).completeSpace_coe
  exact (survivingSpace R L).starProjection_norm_le

omit [CompleteSpace J] in
theorem kernelProjection_fixes (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) {x : H} (hx : x∈survivingSpace R L) :
    kernelProjection R L hR x=x := by
  let : CompleteSpace (survivingSpace R L) := (survivingSpace_closed R L hR).completeSpace_coe
  exact Submodule.starProjection_eq_self_iff.mpr hx

omit [CompleteSpace J] in
theorem kernelProjection_zero (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) {x : H} (hx : x∈(survivingSpace R L)ᗮ) :
    kernelProjection R L hR x=0 := by
  let : CompleteSpace (survivingSpace R L) := (survivingSpace_closed R L hR).completeSpace_coe
  exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hx

/-- Amplifying a fixed stack of observations sends the actual positive
reconstruction operator strongly to the surviving-space projection. The
proof uses the energy identity and density, with no inverse square root. -/
theorem amplified_tendsto_kernelProjection (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (x : H) :
    Tendsto (fun n => amplified R L hR n x) atTop (𝓝 (kernelProjection R L hR x)) := by
  let T (n : ℕ) := amplified R L hR n-kernelProjection R L hR
  have hT (n : ℕ) : ‖T n‖≤2 := by
    exact (norm_sub_le _ _).trans (by linarith [amplified_norm_le R L hR n,kernelProjection_norm_le R L hR])
  let W := AsymptoticStrongConvergence.vanishing T
  let : CompleteSpace W := (AsymptoticStrongConvergence.vanishing_isClosed T hT).completeSpace_coe
  let : CompleteSpace R.range := (reconstruction_range_closed R hR).completeSpace_coe
  have hperp : R.rangeᗮ≤W := by
    intro y hy
    have hp : kernelProjection R L hR y=0 :=
      kernelProjection_zero R L hR (Submodule.orthogonal_le inf_le_left hy)
    change Tendsto (fun n => T n y) atTop (𝓝 0)
    simpa only [T,sub_apply,amplified_zero_of_orthogonal R L hR _ hy,hp,sub_self]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:H)) atTop (𝓝 0))
  have hadj : L.adjoint.range≤W := by
    intro y hy
    obtain ⟨z,rfl⟩ := hy
    have hp : kernelProjection R L hR (L.adjoint z)=0 := by
      apply kernelProjection_zero
      intro u hu
      rw [L.adjoint_inner_right,show L u=0 from hu.2,inner_zero_left]
    change Tendsto (fun n => T n (L.adjoint z)) atTop (𝓝 0)
    simpa only [T,sub_apply,hp,sub_zero] using amplified_adjoint_tendsto R L hR z
  have hker : R.range⊓L.ker≤W := by
    intro y hy
    have hp := kernelProjection_fixes R L hR hy
    change Tendsto (fun n => T n y) atTop (𝓝 0)
    simpa only [T,sub_apply,amplified_fixes R L hR _ hy,hp,sub_self]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:H)) atTop (𝓝 0))
  have hW : W=⊤ := AsymptoticStrongConvergence.eq_top_of_range_kernel R.range W L hperp hadj hker
  have hx : x∈W := by rw [hW]; trivial
  change Tendsto (fun n => amplified R L hR n x-kernelProjection R L hR x) atTop (𝓝 0) at hx
  simpa only [sub_add_cancel,zero_add] using hx.add_const (kernelProjection R L hR x)

#print axioms survivingSpace_closed
#print axioms kernelProjection_norm_le
#print axioms kernelProjection_fixes
#print axioms kernelProjection_zero
#print axioms amplified_tendsto_kernelProjection

end AsymptoticObservation
