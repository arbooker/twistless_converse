module

public import QuantitativeNewGapFrickeSignGapV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open QuantitativeNewGap InnerProductSpace
open scoped InnerProduct
namespace QuantitativeMaass
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def involutionSignSpace (U : H →L[ℂ] H) (s : ℝ) : Submodule ℂ H := (U-(s:ℂ) • 1).ker
instance (U : H →L[ℂ] H) (s : ℝ) : CompleteSpace (involutionSignSpace U s) :=
  inferInstanceAs (CompleteSpace ((U-(s:ℂ) • 1).ker))

theorem involutionSignRow_selfAdjoint (U : H →L[ℂ] H) (hU : IsSelfAdjoint U) (s : ℝ) :
    IsSelfAdjoint (U-(s:ℂ) • 1) := by
  have hs : IsSelfAdjoint ((s:ℂ) • (1:H →L[ℂ] H)) := by
    apply IsSelfAdjoint.smul
    · simp [IsSelfAdjoint]
    · exact IsSelfAdjoint.one _
  exact hU.sub hs

/-- The exact sign projection of an actual self-adjoint involution. -/
theorem involutionSignSpace_projection (U : H →L[ℂ] H) (hU : IsSelfAdjoint U)
    (hUU : Function.Involutive U) (s : ℝ) (hs : s^2=1) (f : H) :
    (involutionSignSpace U s).starProjection f=(1/2:ℂ) • (f+(s:ℂ) • U f) := by
  have hsC : (s:ℂ)*(s:ℂ)=1 := by exact_mod_cast (show s*s=1 by nlinarith)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change U ((1/2:ℂ) • (f+(s:ℂ) • U f))-
      (s:ℂ) • ((1/2:ℂ) • (f+(s:ℂ) • U f))=0
    simp only [map_smul,map_add,hUU f,smul_add,smul_smul]
    have hc : (s:ℂ)*((1/2:ℂ)*(s:ℂ))=(1/2:ℂ) := by
      linear_combination (1/2:ℂ)*hsC
    rw [hc]
    module
  · intro g hg
    have hgU : U g=(s:ℂ) • g := sub_eq_zero.mp hg
    change ⟪f-(1/2:ℂ) • (f+(s:ℂ) • U f),g⟫_ℂ=0
    rw [inner_sub_left,inner_smul_left,inner_add_left,inner_smul_left,
      ←U.adjoint_inner_right,hU.adjoint_eq,hgU,inner_smul_right]
    have hc : (starRingEnd ℂ) (1/2:ℂ)=(1/2:ℂ) := by
      convert Complex.conj_ofReal (1/2:ℝ) using 1 <;> push_cast <;> rfl
    rw [hc,Complex.conj_ofReal]
    linear_combination -(1/2:ℂ)*⟪f,g⟫_ℂ*hsC

theorem involutionSignProjections_commute (U V : H →L[ℂ] H)
    (hU : IsSelfAdjoint U) (hV : IsSelfAdjoint V) (hc : Commute U V) (s t : ℝ) :
    Commute (involutionSignSpace U s).starProjection (involutionSignSpace V t).starProjection := by
  apply kernelProjections_commute
  · exact involutionSignRow_selfAdjoint U hU s
  · exact involutionSignRow_selfAdjoint V hV t
  · exact (hc.sub_right ((Commute.one_right _).smul_right (t:ℂ))).sub_left
      ((Commute.one_left _).smul_left (s:ℂ))

theorem subspace_involutionSign_commute (K : Submodule ℂ H) [CompleteSpace K]
    (U : H →L[ℂ] H) (hU : IsSelfAdjoint U) (hc : Commute K.starProjection U) (s : ℝ) :
    Commute K.starProjection (involutionSignSpace U s).starProjection := by
  have hh := (hc.sub_right ((Commute.one_right _).smul_right (s:ℂ))).eq
  change K.starProjection.comp (involutionSignSpace U s).starProjection=
    (involutionSignSpace U s).starProjection.comp K.starProjection
  apply ContinuousLinearMap.ext
  intro x
  exact QuantitativeEulerOldProjectionBlock.kernel_intertwine K.starProjection _ _
    (involutionSignRow_selfAdjoint U hU s) (involutionSignRow_selfAdjoint U hU s) hh x

#print axioms involutionSignRow_selfAdjoint
#print axioms involutionSignSpace_projection
#print axioms involutionSignProjections_commute
#print axioms subspace_involutionSign_commute
end QuantitativeMaass
