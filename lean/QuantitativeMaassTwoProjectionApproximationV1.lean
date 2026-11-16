module

public import QuantitativeMaassTwoProjectionPowerGapV1
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
open scoped InnerProductSpace
namespace QuantitativeMaass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The same polynomial converges quantitatively to the orthogonal
projection onto the common new space. The only analytic input is the
old-projection coercivity estimate on the actual Hilbert space. -/
theorem two_projection_power_approximation (P Q : E→ₗ[ℂ]E)
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : ∀ w∈U,P w=0 ∧ Q w=0) (γ : ℝ) (hγ : γ≤2)
    (hgap : ∀ v,γ*‖v-U.starProjection v‖^2≤‖P v‖^2+‖Q v‖^2)
    (m : ℕ) (v : E) :
    ‖((1-(1/2:ℂ) • (P+Q))^m) v-U.starProjection v‖^2 ≤
      (1-γ/2)^m*‖v-U.starProjection v‖^2 := by
  let T : E→ₗ[ℂ]E := 1-(1/2:ℂ) • (P+Q)
  have hT : T.IsSymmetric := LinearMap.IsSymmetric.one.sub
    (LinearMap.IsSymmetric.smul (by change star (1/2:ℂ)=(1/2:ℂ); simp) (hP.add hQ))
  have hfix (w : E) (hw : w∈U) : T w=w := by
    change w-(1/2:ℂ) • (P w+Q w)=w
    rw [(hU w hw).1,(hU w hw).2,add_zero,smul_zero,sub_zero]
  have hinv (w : E) (hw : w∈Uᗮ) : T w∈Uᗮ := by
    intro z hz
    rw [←hT z w,hfix z hz]
    exact hw z hz
  have hg (w : E) (hw : w∈Uᗮ) : γ*‖w‖^2≤‖P w‖^2+‖Q w‖^2 := by
    have hh := hgap w
    rw [(U.starProjection_apply_eq_zero_iff).mpr hw,sub_zero] at hh
    exact hh
  have hh := two_projection_filter_power_gap P Q hP hQ hPP hQQ Uᗮ γ hγ hinv hg
    m (v-U.starProjection v) (U.sub_starProjection_mem_orthogonal v)
  have hp (n : ℕ) : (T^n) (U.starProjection v)=U.starProjection v := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Module.End.mul_apply,ih]; exact hfix _ (U.starProjection_apply_mem v)
  change ‖(T^m) (v-U.starProjection v)‖^2 ≤ _ at hh
  rw [map_sub,hp] at hh
  exact hh

#print axioms two_projection_power_approximation
end QuantitativeMaass
