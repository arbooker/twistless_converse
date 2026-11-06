module

public import QuantitativeNewGapTreeHeckeNormV1
public import AsymptoticQuotientNewSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open InnerProductSpace
open scoped InnerProductSpace lp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The angle of two closed subspaces controls their actual projection
energy on the closure of their sum. No closed-sum premise is needed. -/
theorem projection_energy_of_angle (U V : Submodule ℂ E)
    [CompleteSpace U] [CompleteSpace V] {a : ℝ} (ha : 0≤a) (ha1 : a<1)
    (hangle : ∀ u∈U, ∀ v∈V, ‖⟪u,v⟫_ℂ‖≤a*‖u‖*‖v‖)
    (w : E) (hw : w∈(U⊔V).topologicalClosure) :
    (1-a)*‖w‖^2≤‖U.starProjection w‖^2+‖V.starProjection w‖^2 := by
  have hclosed : IsClosed {w : E | (1-a)*‖w‖^2≤
      ‖U.starProjection w‖^2+‖V.starProjection w‖^2} := isClosed_le (by fun_prop) (by fun_prop)
  apply (closure_minimal (s := (U⊔V : Submodule ℂ E)) ?_ hclosed) hw
  intro w hw
  obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hw
  change (1-a)*‖u+v‖^2≤‖U.starProjection (u+v)‖^2+‖V.starProjection (u+v)‖^2
  have hc : 0<1-a := sub_pos.mpr ha1
  have hlo : (1-a)*(‖u‖^2+‖v‖^2)≤‖u+v‖^2 := by
    have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hangle u hu v hv))).1
    rw [norm_add_sq (𝕜:=ℂ)]
    change (1-a)*(‖u‖^2+‖v‖^2)≤‖u‖^2+2*(⟪u,v⟫_ℂ).re+‖v‖^2
    nlinarith [mul_nonneg ha (sq_nonneg (‖u‖-‖v‖))]
  have hip (S : Submodule ℂ E) [CompleteSpace S] (x : E) (hx : x∈S) :
      (⟪x,u+v⟫_ℂ).re≤‖x‖*‖S.starProjection (u+v)‖ := by
    have he := S.inner_starProjection_left_eq_right x (u+v)
    rw [S.starProjection_eq_self_iff.mpr hx] at he
    rw [he]
    exact re_inner_le_norm (𝕜:=ℂ) _ _
  have hhi : ‖u+v‖^2≤‖u‖*‖U.starProjection (u+v)‖+
      ‖v‖*‖V.starProjection (u+v)‖ := by
    have he : ‖u+v‖^2=(⟪u,u+v⟫_ℂ).re+(⟪v,u+v⟫_ℂ).re := by
      rw [← Complex.add_re,← inner_add_left]
      exact norm_sq_eq_re_inner (𝕜:=ℂ) (u+v)
    rw [he]
    exact add_le_add (hip U u hu) (hip V v hv)
  have hs := (sq_le_sq₀ (sq_nonneg ‖u+v‖) (by positivity)).mpr hhi
  have hcs : (‖u+v‖^2)^2≤(‖u‖^2+‖v‖^2)*
      (‖U.starProjection (u+v)‖^2+‖V.starProjection (u+v)‖^2) := by
    nlinarith [sq_nonneg (‖u‖*‖V.starProjection (u+v)‖-
      ‖v‖*‖U.starProjection (u+v)‖)]
  have hb := mul_le_mul_of_nonneg_left hcs hc.le
  have hl := mul_le_mul_of_nonneg_right hlo
    (show 0≤‖U.starProjection (u+v)‖^2+‖V.starProjection (u+v)‖^2 by positivity)
  by_cases hz : ‖u+v‖^2=0
  · simp only [hz,mul_zero]
    positivity
  · have hp : 0<‖u+v‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith

/-- A concrete angle bound gives coercivity away from the common kernel
of the two literal orthogonal projections. -/
theorem projection_complement_gap (U V : Submodule ℂ E)
    [CompleteSpace U] [CompleteSpace V] {a : ℝ} (ha : 0≤a) (ha1 : a<1)
    (hangle : ∀ u∈U, ∀ v∈V, ‖⟪u,v⟫_ℂ‖≤a*‖u‖*‖v‖) (w : E) :
    (1-a)*‖w-(U⊔V)ᗮ.starProjection w‖^2≤
      ‖U.starProjection w‖^2+‖V.starProjection w‖^2 := by
  have hw := (U⊔V)ᗮ.sub_starProjection_mem_orthogonal w
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hw
  have hb := projection_energy_of_angle U V ha ha1 hangle _ hw
  have hzU : U.starProjection ((U⊔V)ᗮ.starProjection w)=0 := by
    apply U.starProjection_apply_eq_zero_iff.mpr
    exact (Submodule.orthogonal_le le_sup_left) ((U⊔V)ᗮ.starProjection_apply_mem w)
  have hzV : V.starProjection ((U⊔V)ᗮ.starProjection w)=0 := by
    apply V.starProjection_apply_eq_zero_iff.mpr
    exact (Submodule.orthogonal_le le_sup_right) ((U⊔V)ᗮ.starProjection_apply_mem w)
  simpa only [map_sub,hzU,hzV,sub_zero] using hb

#print axioms projection_energy_of_angle
#print axioms projection_complement_gap

end QuantitativeNewGap
