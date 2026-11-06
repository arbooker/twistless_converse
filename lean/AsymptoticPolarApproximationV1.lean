module

public import AsymptoticPolarSupportV1
public import AsymptoticObservationKernelLimitV1
public import AsymptoticRepeatedObservationsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPolarIsometry

open ContinuousLinearMap InnerProductSpace Filter AsymptoticObservation
open scoped InnerProduct Topology

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

noncomputable def penaltyRoot (T : H →L[ℂ] J) : H →L[ℂ] H := CFC.sqrt (absolute T)

theorem penaltyRoot_gram (T : H →L[ℂ] J) :
    (penaltyRoot T).adjoint.comp (penaltyRoot T)=absolute T := by
  have ha : (penaltyRoot T).adjoint=penaltyRoot T := (CFC.sqrt_nonneg (absolute T)).star_eq
  rw [ha]
  exact CFC.sqrt_mul_sqrt_self (absolute T) (CFC.sqrt_nonneg _)

theorem penaltyRoot_ker (T : H →L[ℂ] J) : (penaltyRoot T).ker=T.ker := by
  rw [← (penaltyRoot T).ker_adjoint_comp_self,penaltyRoot_gram,absolute_ker]

noncomputable def resolvent (T : H →L[ℂ] J) (n : ℕ) : H →L[ℂ] H :=
  amplified (1 : H →L[ℂ] H) (penaltyRoot T) (fun _ => le_rfl) n

theorem resolvent_normal_formula (T : H →L[ℂ] J) (n : ℕ) :
    normal (1 : H →L[ℂ] H) (((n+1:ℕ):ℂ) • penaltyRoot T)=
      1+(((n+1)^2:ℕ):ℂ) • absolute T := by
  rw [normal_formula,nat_scaled_gram,penaltyRoot_gram]
  simp only [one_def,adjoint_id,id_comp,comp_id]

theorem resolvent_equation (T : H →L[ℂ] J) (n : ℕ) (x : H) :
    resolvent T n x+(((n+1)^2:ℕ):ℂ) • absolute T (resolvent T n x)=x := by
  let L := (((n+1:ℕ):ℂ) • penaltyRoot T)
  have h := (normalEquiv (1 : H →L[ℂ] H) L (fun _ => le_rfl)).apply_symm_apply x
  have he : resolvent T n x=(normalEquiv (1 : H →L[ℂ] H) L (fun _ => le_rfl)).symm x := by
    simp only [resolvent,amplified,operator_apply,one_def,adjoint_id,id_apply,L]
  change normal (1 : H →L[ℂ] H) L ((normalEquiv (1 : H →L[ℂ] H) L (fun _ => le_rfl)).symm x)=x at h
  rw [← he,resolvent_normal_formula] at h
  simpa only [add_apply,one_def,id_apply,smul_apply] using h

theorem resolvent_strong_limit (T : H →L[ℂ] J) (x : H) :
    Tendsto (fun n => resolvent T n x) atTop (𝓝 (T.ker.starProjection x)) := by
  have hk : survivingSpace (1 : H →L[ℂ] H) (penaltyRoot T)=T.ker := by
    have hid : (1 : H →L[ℂ] H).range=⊤ := LinearMap.range_eq_top.mpr (fun x => ⟨x,rfl⟩)
    rw [survivingSpace,hid,top_inf_eq,penaltyRoot_ker]
  have ht := amplified_tendsto_kernelProjection (1 : H →L[ℂ] H) (penaltyRoot T) (fun _ => le_rfl) x
  simpa only [resolvent,kernelProjection,hk] using ht

theorem polar_zero_on_kernel (T : H →L[ℂ] J) {x : H} (hx : x∈T.ker) : polar T x=0 := by
  apply norm_eq_zero.mp
  have hn : ‖polar T x‖=‖T.kerᗮ.starProjection x‖ := by
    simpa only [polar,absolute_closedRange] using partialIsometry_norm T (absolute T) (absolute_norm T) x
  have hz : T.kerᗮ.starProjection x=0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (T.ker.le_orthogonal_orthogonal hx)
  exact hn.trans (by rw [hz,norm_zero])

noncomputable def regularizedPolar (T : H →L[ℂ] J) (n : ℕ) : H →L[ℂ] J :=
  (((n+1)^2:ℕ):ℂ) • T.comp (resolvent T n)

theorem regularizedPolar_formula (T : H →L[ℂ] J) (n : ℕ) :
    regularizedPolar T n=(polar T).comp (1-resolvent T n) := by
  ext x
  have he := resolvent_equation T n x
  have ht := congrArg (fun B : H →L[ℂ] J => B (resolvent T n x)) (polar_factor T)
  change polar T (absolute T (resolvent T n x))=T (resolvent T n x) at ht
  change (((n+1)^2:ℕ):ℂ) • T (resolvent T n x)=polar T (x-resolvent T n x)
  rw [← ht,← map_smul]
  exact congrArg (polar T) (eq_sub_of_add_eq' he)

/-- Regularized polar operators are built from the original operator,
its positive square roots, and coercive observation inverses. They converge
strongly to the constructed polar isometry. -/
theorem regularizedPolar_strong_limit (T : H →L[ℂ] J) (x : H) :
    Tendsto (fun n => regularizedPolar T n x) atTop (𝓝 (polar T x)) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub
    (resolvent_strong_limit T x)
  have hp := (polar T).continuous.tendsto (x-T.ker.starProjection x) |>.comp ht
  have hz : polar T (T.ker.starProjection x)=0 :=
    polar_zero_on_kernel T (T.ker.starProjection_apply_mem x)
  simpa only [regularizedPolar_formula,comp_apply,sub_apply,one_def,id_apply,map_sub,hz,sub_zero,Function.comp_def] using hp

#print axioms penaltyRoot_gram
#print axioms penaltyRoot_ker
#print axioms resolvent_normal_formula
#print axioms resolvent_equation
#print axioms resolvent_strong_limit
#print axioms polar_zero_on_kernel
#print axioms regularizedPolar_formula
#print axioms regularizedPolar_strong_limit

end AsymptoticPolarIsometry
